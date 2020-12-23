%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H3BosyQgcb

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:47 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 728 expanded)
%              Number of leaves         :   38 ( 211 expanded)
%              Depth                    :   45
%              Number of atoms          : 3615 (25428 expanded)
%              Number of equality atoms :   85 ( 809 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(t57_waybel_0,conjecture,(
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
                       => ( r2_yellow_0 @ A @ D ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r2_hidden @ D @ C )
                          & ! [E: $i] :
                              ( ( ( v1_finset_1 @ E )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                             => ~ ( ( r2_yellow_0 @ A @ E )
                                  & ( D
                                    = ( k2_yellow_0 @ A @ E ) ) ) ) ) )
                  & ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                    <=> ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) )).

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
                         => ( r2_yellow_0 @ A @ D ) ) )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ! [E: $i] :
                                ( ( ( v1_finset_1 @ E )
                                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                               => ~ ( ( r2_yellow_0 @ A @ E )
                                    & ( D
                                      = ( k2_yellow_0 @ A @ E ) ) ) ) ) )
                    & ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ B @ D )
                      <=> ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_waybel_0])).

thf('0',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X15 @ X14 ) @ X15 )
      | ( r1_lattice3 @ X14 @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X15 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattice3 @ X14 @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X29: $i] :
      ( ( X29
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X29: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X29 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_lattice3 @ X26 @ X25 @ X27 )
      | ( r1_lattice3 @ X26 @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X29: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( sk_E @ X29 ) )
      | ~ ( r2_hidden @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k2_yellow_0 @ X17 @ X18 ) )
      | ~ ( r1_lattice3 @ X17 @ X18 @ X20 )
      | ( r1_orders_2 @ X17 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( r2_yellow_0 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ X20 @ ( k2_yellow_0 @ X17 @ X18 ) )
      | ~ ( r1_lattice3 @ X17 @ X18 @ X20 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['15','53'])).

thf('55',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_orders_2 @ X14 @ X13 @ ( sk_D @ X13 @ X15 @ X14 ) )
      | ( r1_lattice3 @ X14 @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['55','60'])).

thf('62',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_yellow_0 @ sk_A @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('71',plain,(
    ! [X6: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('72',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('75',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('77',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r3_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r3_orders_2 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('98',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ( r1_lattice3 @ X22 @ ( k1_tarski @ X23 ) @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('107',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('110',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_lattice3 @ X17 @ X18 @ X19 )
      | ( r1_lattice3 @ X17 @ X18 @ ( sk_D_1 @ X19 @ X18 @ X17 ) )
      | ( X19
        = ( k2_yellow_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ X1 ) )
      | ( r1_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ X1 ) )
      | ( r1_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['107','115'])).

thf('117',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('121',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_lattice3 @ X17 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_D_1 @ X19 @ X18 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( X19
        = ( k2_yellow_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['118','126'])).

thf('128',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_lattice3 @ X22 @ ( k1_tarski @ X23 ) @ X21 )
      | ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','132'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','134'])).

thf('136',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_lattice3 @ X17 @ X18 @ X19 )
      | ~ ( r1_orders_2 @ X17 @ ( sk_D_1 @ X19 @ X18 @ X17 ) @ X19 )
      | ( X19
        = ( k2_yellow_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('138',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','141'])).

thf('143',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','143'])).

thf('145',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','145'])).

thf('147',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('149',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X28 ) @ sk_C )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X6: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('152',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('154',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k1_tarski @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['147','160'])).

thf('162',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_lattice3 @ X22 @ ( k1_tarski @ X23 ) @ X21 )
      | ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['65','168'])).

thf('170',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('172',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['170','171'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('173',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('174',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('175',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('176',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('178',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H3BosyQgcb
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.07  % Solved by: fo/fo7.sh
% 0.83/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.07  % done 780 iterations in 0.603s
% 0.83/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.07  % SZS output start Refutation
% 0.83/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.07  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.83/1.07  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.83/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.07  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.83/1.07  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.83/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.07  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.83/1.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.83/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.07  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.83/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.07  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.83/1.07  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.83/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.07  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.83/1.07  thf(sk_E_type, type, sk_E: $i > $i).
% 0.83/1.07  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.83/1.07  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.83/1.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.07  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.83/1.07  thf(t57_waybel_0, conjecture,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.83/1.07         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07           ( ![C:$i]:
% 0.83/1.07             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07               ( ( ( ![D:$i]:
% 0.83/1.07                     ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.07                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.07                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.07                         ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.83/1.07                   ( ![D:$i]:
% 0.83/1.07                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.83/1.07                            ( ![E:$i]:
% 0.83/1.07                              ( ( ( v1_finset_1 @ E ) & 
% 0.83/1.07                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.07                                ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.83/1.07                                     ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.83/1.07                   ( ![D:$i]:
% 0.83/1.07                     ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.07                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.07                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.07                         ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.83/1.07                 ( ![D:$i]:
% 0.83/1.07                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07                     ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.83/1.07                       ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.07    (~( ![A:$i]:
% 0.83/1.07        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.83/1.07            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.83/1.07          ( ![B:$i]:
% 0.83/1.07            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07              ( ![C:$i]:
% 0.83/1.07                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07                  ( ( ( ![D:$i]:
% 0.83/1.07                        ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.07                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.07                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.07                            ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.83/1.07                      ( ![D:$i]:
% 0.83/1.07                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.83/1.07                               ( ![E:$i]:
% 0.83/1.07                                 ( ( ( v1_finset_1 @ E ) & 
% 0.83/1.07                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.07                                   ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.83/1.07                                        ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.83/1.07                      ( ![D:$i]:
% 0.83/1.07                        ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.07                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.07                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.07                            ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.83/1.07                    ( ![D:$i]:
% 0.83/1.07                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07                        ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.83/1.07                          ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.83/1.07    inference('cnf.neg', [status(esa)], [t57_waybel_0])).
% 0.83/1.07  thf('0', plain,
% 0.83/1.07      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07        | ~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('1', plain,
% 0.83/1.07      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.07       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('split', [status(esa)], ['0'])).
% 0.83/1.07  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(d8_lattice3, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_orders_2 @ A ) =>
% 0.83/1.07       ( ![B:$i,C:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.83/1.07             ( ![D:$i]:
% 0.83/1.07               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf('3', plain,
% 0.83/1.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.83/1.07          | (r2_hidden @ (sk_D @ X13 @ X15 @ X14) @ X15)
% 0.83/1.07          | (r1_lattice3 @ X14 @ X15 @ X13)
% 0.83/1.07          | ~ (l1_orders_2 @ X14))),
% 0.83/1.07      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.07  thf('4', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('6', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.07      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.07  thf('7', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('8', plain,
% 0.83/1.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ X13 @ X15 @ X14) @ (u1_struct_0 @ X14))
% 0.83/1.07          | (r1_lattice3 @ X14 @ X15 @ X13)
% 0.83/1.07          | ~ (l1_orders_2 @ X14))),
% 0.83/1.07      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.07  thf('9', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['7', '8'])).
% 0.83/1.07  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('11', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('12', plain,
% 0.83/1.07      (![X29 : $i]:
% 0.83/1.07         (((X29) = (k2_yellow_0 @ sk_A @ (sk_E @ X29)))
% 0.83/1.07          | ~ (r2_hidden @ X29 @ sk_C)
% 0.83/1.07          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('13', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.07  thf('14', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['6', '13'])).
% 0.83/1.07  thf('15', plain,
% 0.83/1.07      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.83/1.07          = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['14'])).
% 0.83/1.07  thf('16', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.07      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.07  thf('17', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('18', plain,
% 0.83/1.07      (![X29 : $i]:
% 0.83/1.07         ((m1_subset_1 @ (sk_E @ X29) @ (k1_zfmisc_1 @ sk_B))
% 0.83/1.07          | ~ (r2_hidden @ X29 @ sk_C)
% 0.83/1.07          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('19', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.83/1.07          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (k1_zfmisc_1 @ sk_B)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.07  thf('20', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.83/1.07           (k1_zfmisc_1 @ sk_B))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['16', '19'])).
% 0.83/1.07  thf('21', plain,
% 0.83/1.07      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.83/1.07         (k1_zfmisc_1 @ sk_B))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['20'])).
% 0.83/1.07  thf(t3_subset, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.07  thf('22', plain,
% 0.83/1.07      (![X3 : $i, X4 : $i]:
% 0.83/1.07         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.07  thf('23', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.83/1.07      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.07  thf('24', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('25', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('split', [status(esa)], ['24'])).
% 0.83/1.07  thf('26', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(t9_yellow_0, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_orders_2 @ A ) =>
% 0.83/1.07       ( ![B:$i,C:$i]:
% 0.83/1.07         ( ( r1_tarski @ B @ C ) =>
% 0.83/1.07           ( ![D:$i]:
% 0.83/1.07             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.83/1.07                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf('27', plain,
% 0.83/1.07      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.83/1.07         (~ (r1_tarski @ X24 @ X25)
% 0.83/1.07          | ~ (r1_lattice3 @ X26 @ X25 @ X27)
% 0.83/1.07          | (r1_lattice3 @ X26 @ X24 @ X27)
% 0.83/1.07          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.83/1.07          | ~ (l1_orders_2 @ X26))),
% 0.83/1.07      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.83/1.07  thf('28', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.07          | ~ (r1_tarski @ X0 @ X1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['26', '27'])).
% 0.83/1.07  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('30', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.07          | ~ (r1_tarski @ X0 @ X1))),
% 0.83/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.07  thf('31', plain,
% 0.83/1.07      ((![X0 : $i]:
% 0.83/1.07          (~ (r1_tarski @ X0 @ sk_B) | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['25', '30'])).
% 0.83/1.07  thf('32', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.83/1.07            sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['23', '31'])).
% 0.83/1.07  thf('33', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.07      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.07  thf('34', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('35', plain,
% 0.83/1.07      (![X29 : $i]:
% 0.83/1.07         ((r2_yellow_0 @ sk_A @ (sk_E @ X29))
% 0.83/1.07          | ~ (r2_hidden @ X29 @ sk_C)
% 0.83/1.07          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('36', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.83/1.07          | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.07  thf('37', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07        | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['33', '36'])).
% 0.83/1.07  thf('38', plain,
% 0.83/1.07      (((r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['37'])).
% 0.83/1.07  thf('39', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('40', plain,
% 0.83/1.07      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.83/1.07          = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['14'])).
% 0.83/1.07  thf(d10_yellow_0, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_orders_2 @ A ) =>
% 0.83/1.07       ( ![B:$i,C:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07           ( ( r2_yellow_0 @ A @ B ) =>
% 0.83/1.07             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.83/1.07               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.83/1.07                 ( ![D:$i]:
% 0.83/1.07                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.83/1.07                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf('41', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.83/1.07         (((X19) != (k2_yellow_0 @ X17 @ X18))
% 0.83/1.07          | ~ (r1_lattice3 @ X17 @ X18 @ X20)
% 0.83/1.07          | (r1_orders_2 @ X17 @ X20 @ X19)
% 0.83/1.07          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (r2_yellow_0 @ X17 @ X18)
% 0.83/1.07          | ~ (l1_orders_2 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.83/1.07  thf('42', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.83/1.07         (~ (l1_orders_2 @ X17)
% 0.83/1.07          | ~ (r2_yellow_0 @ X17 @ X18)
% 0.83/1.07          | ~ (m1_subset_1 @ (k2_yellow_0 @ X17 @ X18) @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.83/1.07          | (r1_orders_2 @ X17 @ X20 @ (k2_yellow_0 @ X17 @ X18))
% 0.83/1.07          | ~ (r1_lattice3 @ X17 @ X18 @ X20))),
% 0.83/1.07      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.07  thf('43', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['40', '42'])).
% 0.83/1.07  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('45', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 0.83/1.07      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.07  thf('46', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['39', '45'])).
% 0.83/1.07  thf('47', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['46'])).
% 0.83/1.07  thf('48', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['38', '47'])).
% 0.83/1.07  thf('49', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['48'])).
% 0.83/1.07  thf('50', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.83/1.07         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.83/1.07            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['32', '49'])).
% 0.83/1.07  thf('51', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('52', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.83/1.07            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.07  thf('53', plain,
% 0.83/1.07      ((((r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.83/1.07          (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['52'])).
% 0.83/1.07  thf('54', plain,
% 0.83/1.07      ((((r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('sup+', [status(thm)], ['15', '53'])).
% 0.83/1.07  thf('55', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.07         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['54'])).
% 0.83/1.07  thf('56', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('57', plain,
% 0.83/1.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.83/1.07          | ~ (r1_orders_2 @ X14 @ X13 @ (sk_D @ X13 @ X15 @ X14))
% 0.83/1.07          | (r1_lattice3 @ X14 @ X15 @ X13)
% 0.83/1.07          | ~ (l1_orders_2 @ X14))),
% 0.83/1.07      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.07  thf('58', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['56', '57'])).
% 0.83/1.07  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('60', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.07  thf('61', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('clc', [status(thm)], ['55', '60'])).
% 0.83/1.07  thf('62', plain,
% 0.83/1.07      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.83/1.07         <= (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('split', [status(esa)], ['0'])).
% 0.83/1.07  thf('63', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.07       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['61', '62'])).
% 0.83/1.07  thf('64', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.07       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('split', [status(esa)], ['24'])).
% 0.83/1.07  thf('65', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('66', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.07      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.07  thf(t63_subset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( r2_hidden @ A @ B ) =>
% 0.83/1.07       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.83/1.07  thf('67', plain,
% 0.83/1.07      (![X1 : $i, X2 : $i]:
% 0.83/1.07         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.83/1.07          | ~ (r2_hidden @ X1 @ X2))),
% 0.83/1.07      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.83/1.07  thf('68', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (k1_zfmisc_1 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['66', '67'])).
% 0.83/1.07  thf('69', plain,
% 0.83/1.07      (![X30 : $i]:
% 0.83/1.07         (((X30) = (k1_xboole_0))
% 0.83/1.07          | (r2_yellow_0 @ sk_A @ X30)
% 0.83/1.07          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ sk_B))
% 0.83/1.07          | ~ (v1_finset_1 @ X30))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('70', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['68', '69'])).
% 0.83/1.07  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.83/1.07  thf('71', plain, (![X6 : $i]: (v1_finset_1 @ (k1_tarski @ X6))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.83/1.07  thf('72', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['70', '71'])).
% 0.83/1.07  thf('73', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('74', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('75', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('76', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf(reflexivity_r3_orders_2, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.83/1.07         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.83/1.07         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.83/1.07  thf('77', plain,
% 0.83/1.07      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.07         ((r3_orders_2 @ X10 @ X11 @ X11)
% 0.83/1.07          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.83/1.07          | ~ (l1_orders_2 @ X10)
% 0.83/1.07          | ~ (v3_orders_2 @ X10)
% 0.83/1.07          | (v2_struct_0 @ X10)
% 0.83/1.07          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10)))),
% 0.83/1.07      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.83/1.07  thf('78', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | ~ (v3_orders_2 @ sk_A)
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['76', '77'])).
% 0.83/1.07  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('81', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.83/1.07  thf('82', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['75', '81'])).
% 0.83/1.07  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('84', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('clc', [status(thm)], ['82', '83'])).
% 0.83/1.07  thf('85', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf(redefinition_r3_orders_2, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.83/1.07         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.83/1.07         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.83/1.07  thf('86', plain,
% 0.83/1.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.83/1.07          | ~ (l1_orders_2 @ X8)
% 0.83/1.07          | ~ (v3_orders_2 @ X8)
% 0.83/1.07          | (v2_struct_0 @ X8)
% 0.83/1.07          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.83/1.07          | (r1_orders_2 @ X8 @ X7 @ X9)
% 0.83/1.07          | ~ (r3_orders_2 @ X8 @ X7 @ X9))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.83/1.07  thf('87', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.83/1.07          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | ~ (v3_orders_2 @ sk_A)
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['85', '86'])).
% 0.83/1.07  thf('88', plain, ((v3_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('90', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.83/1.07          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.83/1.07  thf('91', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['84', '90'])).
% 0.83/1.07  thf('92', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['91'])).
% 0.83/1.07  thf('93', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['74', '92'])).
% 0.83/1.07  thf('94', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | (v2_struct_0 @ sk_A)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['93'])).
% 0.83/1.07  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('96', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('clc', [status(thm)], ['94', '95'])).
% 0.83/1.07  thf('97', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf(t7_yellow_0, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_orders_2 @ A ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07           ( ![C:$i]:
% 0.83/1.07             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.83/1.07                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.83/1.07                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.83/1.07                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.83/1.07                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.83/1.07                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.83/1.07                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.83/1.07                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf('98', plain,
% 0.83/1.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.83/1.07          | ~ (r1_orders_2 @ X22 @ X21 @ X23)
% 0.83/1.07          | (r1_lattice3 @ X22 @ (k1_tarski @ X23) @ X21)
% 0.83/1.07          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.83/1.07          | ~ (l1_orders_2 @ X22))),
% 0.83/1.07      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.83/1.07  thf('99', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['97', '98'])).
% 0.83/1.07  thf('100', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('101', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1))),
% 0.83/1.07      inference('demod', [status(thm)], ['99', '100'])).
% 0.83/1.07  thf('102', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['96', '101'])).
% 0.83/1.07  thf('103', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['102'])).
% 0.83/1.07  thf('104', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('105', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('clc', [status(thm)], ['103', '104'])).
% 0.83/1.07  thf('106', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('107', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['70', '71'])).
% 0.83/1.07  thf('108', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('clc', [status(thm)], ['103', '104'])).
% 0.83/1.07  thf('109', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('110', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.07         (~ (r1_lattice3 @ X17 @ X18 @ X19)
% 0.83/1.07          | (r1_lattice3 @ X17 @ X18 @ (sk_D_1 @ X19 @ X18 @ X17))
% 0.83/1.07          | ((X19) = (k2_yellow_0 @ X17 @ X18))
% 0.83/1.07          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (r2_yellow_0 @ X17 @ X18)
% 0.83/1.07          | ~ (l1_orders_2 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.83/1.07  thf('111', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ X1)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k2_yellow_0 @ sk_A @ X1))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X1 @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['109', '110'])).
% 0.83/1.07  thf('112', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('113', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ X1)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k2_yellow_0 @ sk_A @ X1))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X1 @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['111', '112'])).
% 0.83/1.07  thf('114', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['108', '113'])).
% 0.83/1.07  thf('115', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['114'])).
% 0.83/1.07  thf('116', plain,
% 0.83/1.07      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['107', '115'])).
% 0.83/1.07  thf('117', plain,
% 0.83/1.07      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07          = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['116'])).
% 0.83/1.07  thf('118', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['70', '71'])).
% 0.83/1.07  thf('119', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('clc', [status(thm)], ['103', '104'])).
% 0.83/1.07  thf('120', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf('121', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.07         (~ (r1_lattice3 @ X17 @ X18 @ X19)
% 0.83/1.07          | (m1_subset_1 @ (sk_D_1 @ X19 @ X18 @ X17) @ (u1_struct_0 @ X17))
% 0.83/1.07          | ((X19) = (k2_yellow_0 @ X17 @ X18))
% 0.83/1.07          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (r2_yellow_0 @ X17 @ X18)
% 0.83/1.07          | ~ (l1_orders_2 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.83/1.07  thf('122', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ X1)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k2_yellow_0 @ sk_A @ X1))
% 0.83/1.07          | (m1_subset_1 @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 0.83/1.07             (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['120', '121'])).
% 0.83/1.07  thf('123', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('124', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ X1)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k2_yellow_0 @ sk_A @ X1))
% 0.83/1.07          | (m1_subset_1 @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 0.83/1.07             (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['122', '123'])).
% 0.83/1.07  thf('125', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 0.83/1.07             (u1_struct_0 @ sk_A))
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.83/1.07          | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['119', '124'])).
% 0.83/1.07  thf('126', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 0.83/1.07          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 0.83/1.07          | (m1_subset_1 @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 0.83/1.07              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 0.83/1.07             (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['125'])).
% 0.83/1.07  thf('127', plain,
% 0.83/1.07      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (m1_subset_1 @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07           (u1_struct_0 @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['118', '126'])).
% 0.83/1.07  thf('128', plain,
% 0.83/1.07      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07          = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (m1_subset_1 @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07           (u1_struct_0 @ sk_A))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['127'])).
% 0.83/1.07  thf('129', plain,
% 0.83/1.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.83/1.07          | ~ (r1_lattice3 @ X22 @ (k1_tarski @ X23) @ X21)
% 0.83/1.07          | (r1_orders_2 @ X22 @ X21 @ X23)
% 0.83/1.07          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.83/1.07          | ~ (l1_orders_2 @ X22))),
% 0.83/1.07      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.83/1.07  thf('130', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ 
% 0.83/1.07                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07             X0)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 0.83/1.07               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['128', '129'])).
% 0.83/1.07  thf('131', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('132', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07          | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07              = (k2_yellow_0 @ sk_A @ 
% 0.83/1.07                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ 
% 0.83/1.07             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07             X0)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 0.83/1.07               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['130', '131'])).
% 0.83/1.07  thf('133', plain,
% 0.83/1.07      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (r1_orders_2 @ sk_A @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['117', '132'])).
% 0.83/1.07  thf('134', plain,
% 0.83/1.07      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | (r1_orders_2 @ sk_A @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['133'])).
% 0.83/1.07  thf('135', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (r1_orders_2 @ sk_A @ 
% 0.83/1.07           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['106', '134'])).
% 0.83/1.07  thf('136', plain,
% 0.83/1.07      (((r1_orders_2 @ sk_A @ 
% 0.83/1.07         (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07          (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 0.83/1.07         (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['135'])).
% 0.83/1.07  thf('137', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.07         (~ (r1_lattice3 @ X17 @ X18 @ X19)
% 0.83/1.07          | ~ (r1_orders_2 @ X17 @ (sk_D_1 @ X19 @ X18 @ X17) @ X19)
% 0.83/1.07          | ((X19) = (k2_yellow_0 @ X17 @ X18))
% 0.83/1.07          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (r2_yellow_0 @ X17 @ X18)
% 0.83/1.07          | ~ (l1_orders_2 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.83/1.07  thf('138', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.83/1.07        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ~ (r1_lattice3 @ sk_A @ 
% 0.83/1.07             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['136', '137'])).
% 0.83/1.07  thf('139', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('140', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ~ (r1_lattice3 @ sk_A @ 
% 0.83/1.07             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['138', '139'])).
% 0.83/1.07  thf('141', plain,
% 0.83/1.07      ((~ (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07           (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['140'])).
% 0.83/1.07  thf('142', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['105', '141'])).
% 0.83/1.07  thf('143', plain,
% 0.83/1.07      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['142'])).
% 0.83/1.07  thf('144', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['73', '143'])).
% 0.83/1.07  thf('145', plain,
% 0.83/1.07      ((~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('simplify', [status(thm)], ['144'])).
% 0.83/1.07  thf('146', plain,
% 0.83/1.07      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07            = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['72', '145'])).
% 0.83/1.07  thf('147', plain,
% 0.83/1.07      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 0.83/1.07          = (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['146'])).
% 0.83/1.07  thf('148', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.07             (k1_zfmisc_1 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['66', '67'])).
% 0.83/1.07  thf('149', plain,
% 0.83/1.07      (![X28 : $i]:
% 0.83/1.07         (((X28) = (k1_xboole_0))
% 0.83/1.07          | (r2_hidden @ (k2_yellow_0 @ sk_A @ X28) @ sk_C)
% 0.83/1.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ sk_B))
% 0.83/1.07          | ~ (v1_finset_1 @ X28))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('150', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.07        | (r2_hidden @ 
% 0.83/1.07           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.83/1.07           sk_C)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['148', '149'])).
% 0.83/1.07  thf('151', plain, (![X6 : $i]: (v1_finset_1 @ (k1_tarski @ X6))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.83/1.07  thf('152', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (r2_hidden @ 
% 0.83/1.07           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.83/1.07           sk_C)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['150', '151'])).
% 0.83/1.07  thf('153', plain,
% 0.83/1.07      (![X1 : $i, X2 : $i]:
% 0.83/1.07         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.83/1.07          | ~ (r2_hidden @ X1 @ X2))),
% 0.83/1.07      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.83/1.07  thf('154', plain,
% 0.83/1.07      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | (m1_subset_1 @ 
% 0.83/1.07           (k1_tarski @ 
% 0.83/1.07            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.83/1.07           (k1_zfmisc_1 @ sk_C)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['152', '153'])).
% 0.83/1.07  thf('155', plain,
% 0.83/1.07      (![X3 : $i, X4 : $i]:
% 0.83/1.07         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.07  thf('156', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | (r1_tarski @ 
% 0.83/1.07           (k1_tarski @ 
% 0.83/1.07            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.83/1.07           sk_C))),
% 0.83/1.07      inference('sup-', [status(thm)], ['154', '155'])).
% 0.83/1.07  thf('157', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('split', [status(esa)], ['24'])).
% 0.83/1.07  thf('158', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.07          | ~ (r1_tarski @ X0 @ X1))),
% 0.83/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.07  thf('159', plain,
% 0.83/1.07      ((![X0 : $i]:
% 0.83/1.07          (~ (r1_tarski @ X0 @ sk_C) | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['157', '158'])).
% 0.83/1.07  thf('160', plain,
% 0.83/1.07      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | (r1_lattice3 @ sk_A @ 
% 0.83/1.07            (k1_tarski @ 
% 0.83/1.07             (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.83/1.07            sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['156', '159'])).
% 0.83/1.07  thf('161', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07          sk_D_2)
% 0.83/1.07         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('sup+', [status(thm)], ['147', '160'])).
% 0.83/1.07  thf('162', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.07            sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['161'])).
% 0.83/1.07  thf('163', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('164', plain,
% 0.83/1.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.83/1.07          | ~ (r1_lattice3 @ X22 @ (k1_tarski @ X23) @ X21)
% 0.83/1.07          | (r1_orders_2 @ X22 @ X21 @ X23)
% 0.83/1.07          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.83/1.07          | ~ (l1_orders_2 @ X22))),
% 0.83/1.07      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.83/1.07  thf('165', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (l1_orders_2 @ sk_A)
% 0.83/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['163', '164'])).
% 0.83/1.07  thf('166', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('167', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.83/1.07          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.83/1.07      inference('demod', [status(thm)], ['165', '166'])).
% 0.83/1.07  thf('168', plain,
% 0.83/1.07      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.07              (u1_struct_0 @ sk_A))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['162', '167'])).
% 0.83/1.07  thf('169', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['65', '168'])).
% 0.83/1.07  thf('170', plain,
% 0.83/1.07      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.07         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.07         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['169'])).
% 0.83/1.07  thf('171', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.07          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.07  thf('172', plain,
% 0.83/1.07      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.07         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('clc', [status(thm)], ['170', '171'])).
% 0.83/1.07  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.83/1.07  thf('173', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.83/1.07  thf('174', plain,
% 0.83/1.07      (((~ (v1_xboole_0 @ k1_xboole_0) | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['172', '173'])).
% 0.83/1.07  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.07  thf('175', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('176', plain,
% 0.83/1.07      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.83/1.07         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.07      inference('demod', [status(thm)], ['174', '175'])).
% 0.83/1.07  thf('177', plain,
% 0.83/1.07      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.83/1.07         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.07      inference('split', [status(esa)], ['0'])).
% 0.83/1.07  thf('178', plain,
% 0.83/1.07      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.07       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['176', '177'])).
% 0.83/1.07  thf('179', plain, ($false),
% 0.83/1.07      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '178'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.83/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
