%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3IaBcyKUY5

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:45 EST 2020

% Result     : Theorem 11.16s
% Output     : Refutation 11.16s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 620 expanded)
%              Number of leaves         :   37 ( 184 expanded)
%              Depth                    :   36
%              Number of atoms          : 3383 (20710 expanded)
%              Number of equality atoms :   86 ( 667 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t52_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r1_yellow_0 @ A @ D ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r2_hidden @ D @ C )
                          & ! [E: $i] :
                              ( ( ( v1_finset_1 @ E )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                             => ~ ( ( r1_yellow_0 @ A @ E )
                                  & ( D
                                    = ( k1_yellow_0 @ A @ E ) ) ) ) ) )
                  & ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                    <=> ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r1_yellow_0 @ A @ D ) ) )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ! [E: $i] :
                                ( ( ( v1_finset_1 @ E )
                                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                               => ~ ( ( r1_yellow_0 @ A @ E )
                                    & ( D
                                      = ( k1_yellow_0 @ A @ E ) ) ) ) ) )
                    & ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ B @ D )
                      <=> ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_waybel_0])).

thf('0',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X15 @ X14 ) @ X15 )
      | ( r2_lattice3 @ X14 @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X29: $i] :
      ( ( X29
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_C )
      | ( X29
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X29 ) ) ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X15 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( r2_lattice3 @ X14 @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X29 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ C @ D )
                 => ( r1_lattice3 @ A @ B @ D ) )
                & ( ( r2_lattice3 @ A @ C @ D )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r2_lattice3 @ X26 @ X25 @ X27 )
      | ( r2_lattice3 @ X26 @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X29: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X29 ) )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k1_yellow_0 @ X17 @ X18 ) )
      | ~ ( r2_lattice3 @ X17 @ X18 @ X20 )
      | ( r1_orders_2 @ X17 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( r1_yellow_0 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k1_yellow_0 @ X17 @ X18 ) @ X20 )
      | ~ ( r2_lattice3 @ X17 @ X18 @ X20 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['12','54'])).

thf('56',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_orders_2 @ X14 @ ( sk_D @ X13 @ X15 @ X14 ) @ X13 )
      | ( r2_lattice3 @ X14 @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['56','61'])).

thf('63',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['25'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('73',plain,(
    ! [X10: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('74',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X11 @ X11 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t7_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ B @ C ) )
                & ( ( r1_orders_2 @ A @ B @ C )
                 => ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) )
                & ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ C @ B ) )
                & ( ( r1_orders_2 @ A @ C @ B )
                 => ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_orders_2 @ X22 @ X23 @ X21 )
      | ( r2_lattice3 @ X22 @ ( k1_tarski @ X23 ) @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('94',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('97',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_lattice3 @ X17 @ X18 @ X19 )
      | ( r2_lattice3 @ X17 @ X18 @ ( sk_D_1 @ X19 @ X18 @ X17 ) )
      | ( X19
        = ( k1_yellow_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( r2_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( r2_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('108',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_lattice3 @ X17 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_D_1 @ X19 @ X18 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( X19
        = ( k1_yellow_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_lattice3 @ X22 @ ( k1_tarski @ X23 ) @ X21 )
      | ( r1_orders_2 @ X22 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','119'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','121'])).

thf('123',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_lattice3 @ X17 @ X18 @ X19 )
      | ~ ( r1_orders_2 @ X17 @ X19 @ ( sk_D_1 @ X19 @ X18 @ X17 ) )
      | ( X19
        = ( k1_yellow_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('125',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','128'])).

thf('130',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','130'])).

thf('132',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','132'])).

thf('134',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('136',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X28 ) @ sk_C )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X10: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('139',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('141',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('143',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('144',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_tarski @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['25'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_lattice3 @ X22 @ ( k1_tarski @ X23 ) @ X21 )
      | ( r1_orders_2 @ X22 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['141','154'])).

thf('156',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['134','156'])).

thf('158',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('160',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['158','159'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('161',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('162',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('163',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('164',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','64','65','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3IaBcyKUY5
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 11.16/11.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.16/11.35  % Solved by: fo/fo7.sh
% 11.16/11.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.16/11.35  % done 4764 iterations in 10.901s
% 11.16/11.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.16/11.35  % SZS output start Refutation
% 11.16/11.35  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 11.16/11.35  thf(sk_D_2_type, type, sk_D_2: $i).
% 11.16/11.35  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 11.16/11.35  thf(sk_B_type, type, sk_B: $i).
% 11.16/11.35  thf(sk_C_type, type, sk_C: $i).
% 11.16/11.35  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 11.16/11.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.16/11.35  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 11.16/11.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.16/11.35  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.16/11.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.16/11.35  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.16/11.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.16/11.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.16/11.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.16/11.35  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 11.16/11.35  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 11.16/11.35  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 11.16/11.35  thf(sk_A_type, type, sk_A: $i).
% 11.16/11.35  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 11.16/11.35  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 11.16/11.35  thf(sk_E_type, type, sk_E: $i > $i).
% 11.16/11.35  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 11.16/11.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.16/11.35  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 11.16/11.35  thf(t52_waybel_0, conjecture,
% 11.16/11.35    (![A:$i]:
% 11.16/11.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.16/11.35         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.16/11.35       ( ![B:$i]:
% 11.16/11.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.16/11.35           ( ![C:$i]:
% 11.16/11.35             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.16/11.35               ( ( ( ![D:$i]:
% 11.16/11.35                     ( ( ( v1_finset_1 @ D ) & 
% 11.16/11.35                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 11.16/11.35                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 11.16/11.35                         ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 11.16/11.35                   ( ![D:$i]:
% 11.16/11.35                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35                       ( ~( ( r2_hidden @ D @ C ) & 
% 11.16/11.35                            ( ![E:$i]:
% 11.16/11.35                              ( ( ( v1_finset_1 @ E ) & 
% 11.16/11.35                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 11.16/11.35                                ( ~( ( r1_yellow_0 @ A @ E ) & 
% 11.16/11.35                                     ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 11.16/11.35                   ( ![D:$i]:
% 11.16/11.35                     ( ( ( v1_finset_1 @ D ) & 
% 11.16/11.35                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 11.16/11.35                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 11.16/11.35                         ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 11.16/11.35                 ( ![D:$i]:
% 11.16/11.35                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35                     ( ( r2_lattice3 @ A @ B @ D ) <=>
% 11.16/11.35                       ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 11.16/11.35  thf(zf_stmt_0, negated_conjecture,
% 11.16/11.35    (~( ![A:$i]:
% 11.16/11.35        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.16/11.35            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.16/11.35          ( ![B:$i]:
% 11.16/11.35            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.16/11.35              ( ![C:$i]:
% 11.16/11.35                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.16/11.35                  ( ( ( ![D:$i]:
% 11.16/11.35                        ( ( ( v1_finset_1 @ D ) & 
% 11.16/11.35                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 11.16/11.35                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 11.16/11.35                            ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 11.16/11.35                      ( ![D:$i]:
% 11.16/11.35                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35                          ( ~( ( r2_hidden @ D @ C ) & 
% 11.16/11.35                               ( ![E:$i]:
% 11.16/11.35                                 ( ( ( v1_finset_1 @ E ) & 
% 11.16/11.35                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 11.16/11.35                                   ( ~( ( r1_yellow_0 @ A @ E ) & 
% 11.16/11.35                                        ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 11.16/11.35                      ( ![D:$i]:
% 11.16/11.35                        ( ( ( v1_finset_1 @ D ) & 
% 11.16/11.35                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 11.16/11.35                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 11.16/11.35                            ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 11.16/11.35                    ( ![D:$i]:
% 11.16/11.35                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35                        ( ( r2_lattice3 @ A @ B @ D ) <=>
% 11.16/11.35                          ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 11.16/11.35    inference('cnf.neg', [status(esa)], [t52_waybel_0])).
% 11.16/11.35  thf('0', plain,
% 11.16/11.35      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('1', plain,
% 11.16/11.35      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 11.16/11.35       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.35      inference('split', [status(esa)], ['0'])).
% 11.16/11.35  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf(d9_lattice3, axiom,
% 11.16/11.35    (![A:$i]:
% 11.16/11.35     ( ( l1_orders_2 @ A ) =>
% 11.16/11.35       ( ![B:$i,C:$i]:
% 11.16/11.35         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 11.16/11.35             ( ![D:$i]:
% 11.16/11.35               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 11.16/11.35  thf('3', plain,
% 11.16/11.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.16/11.35         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 11.16/11.35          | (r2_hidden @ (sk_D @ X13 @ X15 @ X14) @ X15)
% 11.16/11.35          | (r2_lattice3 @ X14 @ X15 @ X13)
% 11.16/11.35          | ~ (l1_orders_2 @ X14))),
% 11.16/11.35      inference('cnf', [status(esa)], [d9_lattice3])).
% 11.16/11.35  thf('4', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (l1_orders_2 @ sk_A)
% 11.16/11.35          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 11.16/11.35      inference('sup-', [status(thm)], ['2', '3'])).
% 11.16/11.35  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('6', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 11.16/11.35      inference('demod', [status(thm)], ['4', '5'])).
% 11.16/11.35  thf('7', plain,
% 11.16/11.35      (![X29 : $i]:
% 11.16/11.35         (((X29) = (k1_yellow_0 @ sk_A @ (sk_E @ X29)))
% 11.16/11.35          | ~ (r2_hidden @ X29 @ sk_C)
% 11.16/11.35          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('8', plain,
% 11.16/11.35      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf(t4_subset, axiom,
% 11.16/11.35    (![A:$i,B:$i,C:$i]:
% 11.16/11.35     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 11.16/11.35       ( m1_subset_1 @ A @ C ) ))).
% 11.16/11.35  thf('9', plain,
% 11.16/11.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 11.16/11.35         (~ (r2_hidden @ X7 @ X8)
% 11.16/11.35          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 11.16/11.35          | (m1_subset_1 @ X7 @ X9))),
% 11.16/11.35      inference('cnf', [status(esa)], [t4_subset])).
% 11.16/11.35  thf('10', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 11.16/11.35      inference('sup-', [status(thm)], ['8', '9'])).
% 11.16/11.35  thf('11', plain,
% 11.16/11.35      (![X29 : $i]:
% 11.16/11.35         (~ (r2_hidden @ X29 @ sk_C)
% 11.16/11.35          | ((X29) = (k1_yellow_0 @ sk_A @ (sk_E @ X29))))),
% 11.16/11.35      inference('clc', [status(thm)], ['7', '10'])).
% 11.16/11.35  thf('12', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 11.16/11.35            = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 11.16/11.35      inference('sup-', [status(thm)], ['6', '11'])).
% 11.16/11.35  thf('13', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 11.16/11.35      inference('demod', [status(thm)], ['4', '5'])).
% 11.16/11.35  thf('14', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('15', plain,
% 11.16/11.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.16/11.35         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ X13 @ X15 @ X14) @ (u1_struct_0 @ X14))
% 11.16/11.35          | (r2_lattice3 @ X14 @ X15 @ X13)
% 11.16/11.35          | ~ (l1_orders_2 @ X14))),
% 11.16/11.35      inference('cnf', [status(esa)], [d9_lattice3])).
% 11.16/11.35  thf('16', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (l1_orders_2 @ sk_A)
% 11.16/11.35          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['14', '15'])).
% 11.16/11.35  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('18', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.35  thf('19', plain,
% 11.16/11.35      (![X29 : $i]:
% 11.16/11.35         ((m1_subset_1 @ (sk_E @ X29) @ (k1_zfmisc_1 @ sk_B))
% 11.16/11.35          | ~ (r2_hidden @ X29 @ sk_C)
% 11.16/11.35          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('20', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 11.16/11.35          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.35             (k1_zfmisc_1 @ sk_B)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['18', '19'])).
% 11.16/11.35  thf('21', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 11.16/11.35           (k1_zfmisc_1 @ sk_B))
% 11.16/11.35        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('sup-', [status(thm)], ['13', '20'])).
% 11.16/11.35  thf('22', plain,
% 11.16/11.35      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 11.16/11.35         (k1_zfmisc_1 @ sk_B))
% 11.16/11.35        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('simplify', [status(thm)], ['21'])).
% 11.16/11.35  thf(t3_subset, axiom,
% 11.16/11.35    (![A:$i,B:$i]:
% 11.16/11.35     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.16/11.35  thf('23', plain,
% 11.16/11.35      (![X4 : $i, X5 : $i]:
% 11.16/11.35         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 11.16/11.35      inference('cnf', [status(esa)], [t3_subset])).
% 11.16/11.35  thf('24', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 11.16/11.35      inference('sup-', [status(thm)], ['22', '23'])).
% 11.16/11.35  thf('25', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('26', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('split', [status(esa)], ['25'])).
% 11.16/11.35  thf('27', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf(t9_yellow_0, axiom,
% 11.16/11.35    (![A:$i]:
% 11.16/11.35     ( ( l1_orders_2 @ A ) =>
% 11.16/11.35       ( ![B:$i,C:$i]:
% 11.16/11.35         ( ( r1_tarski @ B @ C ) =>
% 11.16/11.35           ( ![D:$i]:
% 11.16/11.35             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 11.16/11.35                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 11.16/11.35  thf('28', plain,
% 11.16/11.35      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 11.16/11.35         (~ (r1_tarski @ X24 @ X25)
% 11.16/11.35          | ~ (r2_lattice3 @ X26 @ X25 @ X27)
% 11.16/11.35          | (r2_lattice3 @ X26 @ X24 @ X27)
% 11.16/11.35          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 11.16/11.35          | ~ (l1_orders_2 @ X26))),
% 11.16/11.35      inference('cnf', [status(esa)], [t9_yellow_0])).
% 11.16/11.35  thf('29', plain,
% 11.16/11.35      (![X0 : $i, X1 : $i]:
% 11.16/11.35         (~ (l1_orders_2 @ sk_A)
% 11.16/11.35          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 11.16/11.35          | ~ (r1_tarski @ X0 @ X1))),
% 11.16/11.35      inference('sup-', [status(thm)], ['27', '28'])).
% 11.16/11.35  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('31', plain,
% 11.16/11.35      (![X0 : $i, X1 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 11.16/11.35          | ~ (r1_tarski @ X0 @ X1))),
% 11.16/11.35      inference('demod', [status(thm)], ['29', '30'])).
% 11.16/11.35  thf('32', plain,
% 11.16/11.35      ((![X0 : $i]:
% 11.16/11.35          (~ (r1_tarski @ X0 @ sk_B) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['26', '31'])).
% 11.16/11.35  thf('33', plain,
% 11.16/11.35      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 11.16/11.35            sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['24', '32'])).
% 11.16/11.35  thf('34', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 11.16/11.35      inference('demod', [status(thm)], ['4', '5'])).
% 11.16/11.35  thf('35', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.35  thf('36', plain,
% 11.16/11.35      (![X29 : $i]:
% 11.16/11.35         ((r1_yellow_0 @ sk_A @ (sk_E @ X29))
% 11.16/11.35          | ~ (r2_hidden @ X29 @ sk_C)
% 11.16/11.35          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('37', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 11.16/11.35          | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 11.16/11.35      inference('sup-', [status(thm)], ['35', '36'])).
% 11.16/11.35  thf('38', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 11.16/11.35        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('sup-', [status(thm)], ['34', '37'])).
% 11.16/11.35  thf('39', plain,
% 11.16/11.35      (((r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 11.16/11.35        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('simplify', [status(thm)], ['38'])).
% 11.16/11.35  thf('40', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.35  thf('41', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 11.16/11.35            = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 11.16/11.35      inference('sup-', [status(thm)], ['6', '11'])).
% 11.16/11.35  thf(d9_yellow_0, axiom,
% 11.16/11.35    (![A:$i]:
% 11.16/11.35     ( ( l1_orders_2 @ A ) =>
% 11.16/11.35       ( ![B:$i,C:$i]:
% 11.16/11.35         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35           ( ( r1_yellow_0 @ A @ B ) =>
% 11.16/11.35             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 11.16/11.35               ( ( r2_lattice3 @ A @ B @ C ) & 
% 11.16/11.35                 ( ![D:$i]:
% 11.16/11.35                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 11.16/11.35                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 11.16/11.35  thf('42', plain,
% 11.16/11.35      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 11.16/11.35         (((X19) != (k1_yellow_0 @ X17 @ X18))
% 11.16/11.35          | ~ (r2_lattice3 @ X17 @ X18 @ X20)
% 11.16/11.35          | (r1_orders_2 @ X17 @ X19 @ X20)
% 11.16/11.35          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 11.16/11.35          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 11.16/11.35          | ~ (r1_yellow_0 @ X17 @ X18)
% 11.16/11.35          | ~ (l1_orders_2 @ X17))),
% 11.16/11.35      inference('cnf', [status(esa)], [d9_yellow_0])).
% 11.16/11.35  thf('43', plain,
% 11.16/11.35      (![X17 : $i, X18 : $i, X20 : $i]:
% 11.16/11.35         (~ (l1_orders_2 @ X17)
% 11.16/11.35          | ~ (r1_yellow_0 @ X17 @ X18)
% 11.16/11.35          | ~ (m1_subset_1 @ (k1_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17))
% 11.16/11.35          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 11.16/11.35          | (r1_orders_2 @ X17 @ (k1_yellow_0 @ X17 @ X18) @ X20)
% 11.16/11.35          | ~ (r2_lattice3 @ X17 @ X18 @ X20))),
% 11.16/11.35      inference('simplify', [status(thm)], ['42'])).
% 11.16/11.35  thf('44', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 11.16/11.35          | (r1_orders_2 @ sk_A @ 
% 11.16/11.35             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 11.16/11.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 11.16/11.35          | ~ (l1_orders_2 @ sk_A))),
% 11.16/11.35      inference('sup-', [status(thm)], ['41', '43'])).
% 11.16/11.35  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('46', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 11.16/11.35          | (r1_orders_2 @ sk_A @ 
% 11.16/11.35             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 11.16/11.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 11.16/11.35      inference('demod', [status(thm)], ['44', '45'])).
% 11.16/11.35  thf('47', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 11.16/11.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | (r1_orders_2 @ sk_A @ 
% 11.16/11.35             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 11.16/11.35          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 11.16/11.35          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('sup-', [status(thm)], ['40', '46'])).
% 11.16/11.35  thf('48', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 11.16/11.35          | (r1_orders_2 @ sk_A @ 
% 11.16/11.35             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 11.16/11.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 11.16/11.35          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('simplify', [status(thm)], ['47'])).
% 11.16/11.35  thf('49', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | (r1_orders_2 @ sk_A @ 
% 11.16/11.35             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 11.16/11.35          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0))),
% 11.16/11.35      inference('sup-', [status(thm)], ['39', '48'])).
% 11.16/11.35  thf('50', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 11.16/11.35          | (r1_orders_2 @ sk_A @ 
% 11.16/11.35             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 11.16/11.35          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.35          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 11.16/11.35      inference('simplify', [status(thm)], ['49'])).
% 11.16/11.35  thf('51', plain,
% 11.16/11.35      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 11.16/11.35         | (r1_orders_2 @ sk_A @ 
% 11.16/11.35            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 11.16/11.35            sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['33', '50'])).
% 11.16/11.35  thf('52', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('53', plain,
% 11.16/11.35      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | (r1_orders_2 @ sk_A @ 
% 11.16/11.35            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 11.16/11.35            sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('demod', [status(thm)], ['51', '52'])).
% 11.16/11.35  thf('54', plain,
% 11.16/11.35      ((((r1_orders_2 @ sk_A @ 
% 11.16/11.35          (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 11.16/11.35          sk_D_2)
% 11.16/11.35         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('simplify', [status(thm)], ['53'])).
% 11.16/11.35  thf('55', plain,
% 11.16/11.35      ((((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 11.16/11.35         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('sup+', [status(thm)], ['12', '54'])).
% 11.16/11.35  thf('56', plain,
% 11.16/11.35      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 11.16/11.35         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('simplify', [status(thm)], ['55'])).
% 11.16/11.35  thf('57', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('58', plain,
% 11.16/11.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.16/11.35         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 11.16/11.35          | ~ (r1_orders_2 @ X14 @ (sk_D @ X13 @ X15 @ X14) @ X13)
% 11.16/11.35          | (r2_lattice3 @ X14 @ X15 @ X13)
% 11.16/11.35          | ~ (l1_orders_2 @ X14))),
% 11.16/11.35      inference('cnf', [status(esa)], [d9_lattice3])).
% 11.16/11.35  thf('59', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         (~ (l1_orders_2 @ sk_A)
% 11.16/11.35          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 11.16/11.35      inference('sup-', [status(thm)], ['57', '58'])).
% 11.16/11.35  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('61', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 11.16/11.35      inference('demod', [status(thm)], ['59', '60'])).
% 11.16/11.35  thf('62', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 11.16/11.35         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.35      inference('clc', [status(thm)], ['56', '61'])).
% 11.16/11.35  thf('63', plain,
% 11.16/11.35      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 11.16/11.35         <= (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.35      inference('split', [status(esa)], ['0'])).
% 11.16/11.35  thf('64', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 11.16/11.35       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.35      inference('sup-', [status(thm)], ['62', '63'])).
% 11.16/11.35  thf('65', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 11.16/11.35       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.35      inference('split', [status(esa)], ['25'])).
% 11.16/11.35  thf('66', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 11.16/11.35      inference('demod', [status(thm)], ['4', '5'])).
% 11.16/11.35  thf(l1_zfmisc_1, axiom,
% 11.16/11.35    (![A:$i,B:$i]:
% 11.16/11.35     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 11.16/11.35  thf('67', plain,
% 11.16/11.35      (![X1 : $i, X3 : $i]:
% 11.16/11.35         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 11.16/11.35      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 11.16/11.35  thf('68', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (r1_tarski @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ X0))),
% 11.16/11.35      inference('sup-', [status(thm)], ['66', '67'])).
% 11.16/11.35  thf('69', plain,
% 11.16/11.35      (![X4 : $i, X6 : $i]:
% 11.16/11.35         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 11.16/11.35      inference('cnf', [status(esa)], [t3_subset])).
% 11.16/11.35  thf('70', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.35             (k1_zfmisc_1 @ X0)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['68', '69'])).
% 11.16/11.35  thf('71', plain,
% 11.16/11.35      (![X30 : $i]:
% 11.16/11.35         (((X30) = (k1_xboole_0))
% 11.16/11.35          | (r1_yellow_0 @ sk_A @ X30)
% 11.16/11.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ sk_B))
% 11.16/11.35          | ~ (v1_finset_1 @ X30))),
% 11.16/11.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.35  thf('72', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.35        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.35        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.35        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.35      inference('sup-', [status(thm)], ['70', '71'])).
% 11.16/11.35  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 11.16/11.35  thf('73', plain, (![X10 : $i]: (v1_finset_1 @ (k1_tarski @ X10))),
% 11.16/11.35      inference('cnf', [status(esa)], [fc1_finset_1])).
% 11.16/11.35  thf('74', plain,
% 11.16/11.35      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.35        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.35        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.35      inference('demod', [status(thm)], ['72', '73'])).
% 11.16/11.35  thf('75', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.35  thf('76', plain,
% 11.16/11.35      (![X0 : $i]:
% 11.16/11.35         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.35          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.35      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.35  thf(t24_orders_2, axiom,
% 11.16/11.35    (![A:$i]:
% 11.16/11.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.16/11.35       ( ![B:$i]:
% 11.16/11.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.35           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 11.16/11.36  thf('77', plain,
% 11.16/11.36      (![X11 : $i, X12 : $i]:
% 11.16/11.36         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 11.16/11.36          | (r1_orders_2 @ X12 @ X11 @ X11)
% 11.16/11.36          | ~ (l1_orders_2 @ X12)
% 11.16/11.36          | ~ (v3_orders_2 @ X12)
% 11.16/11.36          | (v2_struct_0 @ X12))),
% 11.16/11.36      inference('cnf', [status(esa)], [t24_orders_2])).
% 11.16/11.36  thf('78', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (v2_struct_0 @ sk_A)
% 11.16/11.36          | ~ (v3_orders_2 @ sk_A)
% 11.16/11.36          | ~ (l1_orders_2 @ sk_A)
% 11.16/11.36          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['76', '77'])).
% 11.16/11.36  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('81', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (v2_struct_0 @ sk_A)
% 11.16/11.36          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['78', '79', '80'])).
% 11.16/11.36  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('83', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('clc', [status(thm)], ['81', '82'])).
% 11.16/11.36  thf('84', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.36  thf(t7_yellow_0, axiom,
% 11.16/11.36    (![A:$i]:
% 11.16/11.36     ( ( l1_orders_2 @ A ) =>
% 11.16/11.36       ( ![B:$i]:
% 11.16/11.36         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.36           ( ![C:$i]:
% 11.16/11.36             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.16/11.36               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 11.16/11.36                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 11.16/11.36                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 11.16/11.36                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 11.16/11.36                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 11.16/11.36                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 11.16/11.36                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 11.16/11.36                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 11.16/11.36  thf('85', plain,
% 11.16/11.36      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.16/11.36         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 11.16/11.36          | ~ (r1_orders_2 @ X22 @ X23 @ X21)
% 11.16/11.36          | (r2_lattice3 @ X22 @ (k1_tarski @ X23) @ X21)
% 11.16/11.36          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 11.16/11.36          | ~ (l1_orders_2 @ X22))),
% 11.16/11.36      inference('cnf', [status(esa)], [t7_yellow_0])).
% 11.16/11.36  thf('86', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (l1_orders_2 @ sk_A)
% 11.16/11.36          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 11.16/11.36          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['84', '85'])).
% 11.16/11.36  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('88', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 11.16/11.36          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['86', '87'])).
% 11.16/11.36  thf('89', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 11.16/11.36          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('sup-', [status(thm)], ['83', '88'])).
% 11.16/11.36  thf('90', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['89'])).
% 11.16/11.36  thf('91', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.36  thf('92', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('clc', [status(thm)], ['90', '91'])).
% 11.16/11.36  thf('93', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.36  thf('94', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('demod', [status(thm)], ['72', '73'])).
% 11.16/11.36  thf('95', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('clc', [status(thm)], ['90', '91'])).
% 11.16/11.36  thf('96', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.36  thf('97', plain,
% 11.16/11.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.16/11.36         (~ (r2_lattice3 @ X17 @ X18 @ X19)
% 11.16/11.36          | (r2_lattice3 @ X17 @ X18 @ (sk_D_1 @ X19 @ X18 @ X17))
% 11.16/11.36          | ((X19) = (k1_yellow_0 @ X17 @ X18))
% 11.16/11.36          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 11.16/11.36          | ~ (r1_yellow_0 @ X17 @ X18)
% 11.16/11.36          | ~ (l1_orders_2 @ X17))),
% 11.16/11.36      inference('cnf', [status(esa)], [d9_yellow_0])).
% 11.16/11.36  thf('98', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (l1_orders_2 @ sk_A)
% 11.16/11.36          | ~ (r1_yellow_0 @ sk_A @ X1)
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X1 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['96', '97'])).
% 11.16/11.36  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('100', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (r1_yellow_0 @ sk_A @ X1)
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X1 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['98', '99'])).
% 11.16/11.36  thf('101', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 11.16/11.36              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 11.16/11.36          | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('sup-', [status(thm)], ['95', '100'])).
% 11.16/11.36  thf('102', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 11.16/11.36              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['101'])).
% 11.16/11.36  thf('103', plain,
% 11.16/11.36      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 11.16/11.36      inference('sup-', [status(thm)], ['94', '102'])).
% 11.16/11.36  thf('104', plain,
% 11.16/11.36      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('simplify', [status(thm)], ['103'])).
% 11.16/11.36  thf('105', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('demod', [status(thm)], ['72', '73'])).
% 11.16/11.36  thf('106', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('clc', [status(thm)], ['90', '91'])).
% 11.16/11.36  thf('107', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['16', '17'])).
% 11.16/11.36  thf('108', plain,
% 11.16/11.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.16/11.36         (~ (r2_lattice3 @ X17 @ X18 @ X19)
% 11.16/11.36          | (m1_subset_1 @ (sk_D_1 @ X19 @ X18 @ X17) @ (u1_struct_0 @ X17))
% 11.16/11.36          | ((X19) = (k1_yellow_0 @ X17 @ X18))
% 11.16/11.36          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 11.16/11.36          | ~ (r1_yellow_0 @ X17 @ X18)
% 11.16/11.36          | ~ (l1_orders_2 @ X17))),
% 11.16/11.36      inference('cnf', [status(esa)], [d9_yellow_0])).
% 11.16/11.36  thf('109', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (l1_orders_2 @ sk_A)
% 11.16/11.36          | ~ (r1_yellow_0 @ sk_A @ X1)
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 11.16/11.36          | (m1_subset_1 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 11.16/11.36             (u1_struct_0 @ sk_A))
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['107', '108'])).
% 11.16/11.36  thf('110', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('111', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (r1_yellow_0 @ sk_A @ X1)
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 11.16/11.36          | (m1_subset_1 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 11.16/11.36             (u1_struct_0 @ sk_A))
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['109', '110'])).
% 11.16/11.36  thf('112', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 11.16/11.36             (u1_struct_0 @ sk_A))
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 11.16/11.36              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 11.16/11.36          | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('sup-', [status(thm)], ['106', '111'])).
% 11.16/11.36  thf('113', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 11.16/11.36          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 11.16/11.36              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 11.16/11.36          | (m1_subset_1 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 11.16/11.36              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 11.16/11.36             (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['112'])).
% 11.16/11.36  thf('114', plain,
% 11.16/11.36      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (m1_subset_1 @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 11.16/11.36           (u1_struct_0 @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 11.16/11.36      inference('sup-', [status(thm)], ['105', '113'])).
% 11.16/11.36  thf('115', plain,
% 11.16/11.36      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (m1_subset_1 @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 11.16/11.36           (u1_struct_0 @ sk_A))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('simplify', [status(thm)], ['114'])).
% 11.16/11.36  thf('116', plain,
% 11.16/11.36      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.16/11.36         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 11.16/11.36          | ~ (r2_lattice3 @ X22 @ (k1_tarski @ X23) @ X21)
% 11.16/11.36          | (r1_orders_2 @ X22 @ X23 @ X21)
% 11.16/11.36          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 11.16/11.36          | ~ (l1_orders_2 @ X22))),
% 11.16/11.36      inference('cnf', [status(esa)], [t7_yellow_0])).
% 11.16/11.36  thf('117', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36              = (k1_yellow_0 @ sk_A @ 
% 11.16/11.36                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36          | ~ (l1_orders_2 @ sk_A)
% 11.16/11.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r1_orders_2 @ sk_A @ X0 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 11.16/11.36               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['115', '116'])).
% 11.16/11.36  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('119', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36          | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36              = (k1_yellow_0 @ sk_A @ 
% 11.16/11.36                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r1_orders_2 @ sk_A @ X0 @ 
% 11.16/11.36             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 11.16/11.36               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['117', '118'])).
% 11.16/11.36  thf('120', plain,
% 11.16/11.36      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['104', '119'])).
% 11.16/11.36  thf('121', plain,
% 11.16/11.36      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('simplify', [status(thm)], ['120'])).
% 11.16/11.36  thf('122', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['93', '121'])).
% 11.16/11.36  thf('123', plain,
% 11.16/11.36      (((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36         (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 11.16/11.36          (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['122'])).
% 11.16/11.36  thf('124', plain,
% 11.16/11.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.16/11.36         (~ (r2_lattice3 @ X17 @ X18 @ X19)
% 11.16/11.36          | ~ (r1_orders_2 @ X17 @ X19 @ (sk_D_1 @ X19 @ X18 @ X17))
% 11.16/11.36          | ((X19) = (k1_yellow_0 @ X17 @ X18))
% 11.16/11.36          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 11.16/11.36          | ~ (r1_yellow_0 @ X17 @ X18)
% 11.16/11.36          | ~ (l1_orders_2 @ X17))),
% 11.16/11.36      inference('cnf', [status(esa)], [d9_yellow_0])).
% 11.16/11.36  thf('125', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ~ (l1_orders_2 @ sk_A)
% 11.16/11.36        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ~ (r2_lattice3 @ sk_A @ 
% 11.16/11.36             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['123', '124'])).
% 11.16/11.36  thf('126', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('127', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ~ (r2_lattice3 @ sk_A @ 
% 11.16/11.36             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 11.16/11.36             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 11.16/11.36      inference('demod', [status(thm)], ['125', '126'])).
% 11.16/11.36  thf('128', plain,
% 11.16/11.36      ((~ (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 11.16/11.36           (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 11.16/11.36        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['127'])).
% 11.16/11.36  thf('129', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['92', '128'])).
% 11.16/11.36  thf('130', plain,
% 11.16/11.36      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 11.16/11.36        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['129'])).
% 11.16/11.36  thf('131', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))),
% 11.16/11.36      inference('sup-', [status(thm)], ['75', '130'])).
% 11.16/11.36  thf('132', plain,
% 11.16/11.36      ((~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.36      inference('simplify', [status(thm)], ['131'])).
% 11.16/11.36  thf('133', plain,
% 11.16/11.36      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 11.16/11.36      inference('sup-', [status(thm)], ['74', '132'])).
% 11.16/11.36  thf('134', plain,
% 11.16/11.36      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 11.16/11.36          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('simplify', [status(thm)], ['133'])).
% 11.16/11.36  thf('135', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 11.16/11.36             (k1_zfmisc_1 @ X0)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['68', '69'])).
% 11.16/11.36  thf('136', plain,
% 11.16/11.36      (![X28 : $i]:
% 11.16/11.36         (((X28) = (k1_xboole_0))
% 11.16/11.36          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X28) @ sk_C)
% 11.16/11.36          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ sk_B))
% 11.16/11.36          | ~ (v1_finset_1 @ X28))),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('137', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 11.16/11.36        | (r2_hidden @ 
% 11.16/11.36           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36           sk_C)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['135', '136'])).
% 11.16/11.36  thf('138', plain, (![X10 : $i]: (v1_finset_1 @ (k1_tarski @ X10))),
% 11.16/11.36      inference('cnf', [status(esa)], [fc1_finset_1])).
% 11.16/11.36  thf('139', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_hidden @ 
% 11.16/11.36           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36           sk_C)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('demod', [status(thm)], ['137', '138'])).
% 11.16/11.36  thf('140', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 11.16/11.36      inference('sup-', [status(thm)], ['8', '9'])).
% 11.16/11.36  thf('141', plain,
% 11.16/11.36      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (m1_subset_1 @ 
% 11.16/11.36           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36           (u1_struct_0 @ sk_A)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['139', '140'])).
% 11.16/11.36  thf('142', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r2_hidden @ 
% 11.16/11.36           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36           sk_C)
% 11.16/11.36        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 11.16/11.36      inference('demod', [status(thm)], ['137', '138'])).
% 11.16/11.36  thf('143', plain,
% 11.16/11.36      (![X1 : $i, X3 : $i]:
% 11.16/11.36         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 11.16/11.36      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 11.16/11.36  thf('144', plain,
% 11.16/11.36      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36        | (r1_tarski @ 
% 11.16/11.36           (k1_tarski @ 
% 11.16/11.36            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 11.16/11.36           sk_C))),
% 11.16/11.36      inference('sup-', [status(thm)], ['142', '143'])).
% 11.16/11.36  thf('145', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('split', [status(esa)], ['25'])).
% 11.16/11.36  thf('146', plain,
% 11.16/11.36      (![X0 : $i, X1 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 11.16/11.36          | ~ (r1_tarski @ X0 @ X1))),
% 11.16/11.36      inference('demod', [status(thm)], ['29', '30'])).
% 11.16/11.36  thf('147', plain,
% 11.16/11.36      ((![X0 : $i]:
% 11.16/11.36          (~ (r1_tarski @ X0 @ sk_C) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['145', '146'])).
% 11.16/11.36  thf('148', plain,
% 11.16/11.36      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r2_lattice3 @ sk_A @ 
% 11.16/11.36            (k1_tarski @ 
% 11.16/11.36             (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 11.16/11.36            sk_D_2)))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['144', '147'])).
% 11.16/11.36  thf('149', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('150', plain,
% 11.16/11.36      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.16/11.36         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 11.16/11.36          | ~ (r2_lattice3 @ X22 @ (k1_tarski @ X23) @ X21)
% 11.16/11.36          | (r1_orders_2 @ X22 @ X23 @ X21)
% 11.16/11.36          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 11.16/11.36          | ~ (l1_orders_2 @ X22))),
% 11.16/11.36      inference('cnf', [status(esa)], [t7_yellow_0])).
% 11.16/11.36  thf('151', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (~ (l1_orders_2 @ sk_A)
% 11.16/11.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 11.16/11.36      inference('sup-', [status(thm)], ['149', '150'])).
% 11.16/11.36  thf('152', plain, ((l1_orders_2 @ sk_A)),
% 11.16/11.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.16/11.36  thf('153', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.16/11.36          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 11.16/11.36      inference('demod', [status(thm)], ['151', '152'])).
% 11.16/11.36  thf('154', plain,
% 11.16/11.36      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | (r1_orders_2 @ sk_A @ 
% 11.16/11.36            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36            sk_D_2)
% 11.16/11.36         | ~ (m1_subset_1 @ 
% 11.16/11.36              (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36              (u1_struct_0 @ sk_A))))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['148', '153'])).
% 11.16/11.36  thf('155', plain,
% 11.16/11.36      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r1_orders_2 @ sk_A @ 
% 11.16/11.36            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36            sk_D_2)
% 11.16/11.36         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['141', '154'])).
% 11.16/11.36  thf('156', plain,
% 11.16/11.36      ((((r1_orders_2 @ sk_A @ 
% 11.16/11.36          (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 11.16/11.36          sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('simplify', [status(thm)], ['155'])).
% 11.16/11.36  thf('157', plain,
% 11.16/11.36      ((((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('sup+', [status(thm)], ['134', '156'])).
% 11.16/11.36  thf('158', plain,
% 11.16/11.36      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 11.16/11.36         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('simplify', [status(thm)], ['157'])).
% 11.16/11.36  thf('159', plain,
% 11.16/11.36      (![X0 : $i]:
% 11.16/11.36         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 11.16/11.36          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 11.16/11.36      inference('demod', [status(thm)], ['59', '60'])).
% 11.16/11.36  thf('160', plain,
% 11.16/11.36      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 11.16/11.36         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('clc', [status(thm)], ['158', '159'])).
% 11.16/11.36  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 11.16/11.36  thf('161', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 11.16/11.36      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 11.16/11.36  thf('162', plain,
% 11.16/11.36      (((~ (v1_xboole_0 @ k1_xboole_0) | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('sup-', [status(thm)], ['160', '161'])).
% 11.16/11.36  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.16/11.36  thf('163', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.16/11.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.16/11.36  thf('164', plain,
% 11.16/11.36      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 11.16/11.36         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 11.16/11.36      inference('demod', [status(thm)], ['162', '163'])).
% 11.16/11.36  thf('165', plain,
% 11.16/11.36      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 11.16/11.36         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 11.16/11.36      inference('split', [status(esa)], ['0'])).
% 11.16/11.36  thf('166', plain,
% 11.16/11.36      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 11.16/11.36       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 11.16/11.36      inference('sup-', [status(thm)], ['164', '165'])).
% 11.16/11.36  thf('167', plain, ($false),
% 11.16/11.36      inference('sat_resolution*', [status(thm)], ['1', '64', '65', '166'])).
% 11.16/11.36  
% 11.16/11.36  % SZS output end Refutation
% 11.16/11.36  
% 11.16/11.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
