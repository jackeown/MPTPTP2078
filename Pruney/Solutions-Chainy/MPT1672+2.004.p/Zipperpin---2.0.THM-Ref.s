%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WgMuDL9IY6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:45 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 737 expanded)
%              Number of leaves         :   38 ( 214 expanded)
%              Depth                    :   45
%              Number of atoms          : 3601 (25482 expanded)
%              Number of equality atoms :   84 ( 808 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X16 @ X15 ) @ X16 )
      | ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
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
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X30: $i] :
      ( ( X30
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X30 ) ) )
      | ~ ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X30 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r2_lattice3 @ X27 @ X26 @ X28 )
      | ( r2_lattice3 @ X27 @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 )
      | ( r1_orders_2 @ X18 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ ( k1_yellow_0 @ X18 @ X19 ) @ X21 )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['15','53'])).

thf('55',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ ( sk_D @ X14 @ X16 @ X15 ) @ X14 )
      | ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['55','60'])).

thf('62',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X31 ) ) ),
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
    ! [X7: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X7 ) ) ),
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
    inference(demod,[status(thm)],['9','10'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
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

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r3_orders_2 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
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

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_orders_2 @ X9 @ X8 @ X10 )
      | ~ ( r3_orders_2 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
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

thf('100',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_orders_2 @ X23 @ X24 @ X22 )
      | ( r2_lattice3 @ X23 @ ( k1_tarski @ X24 ) @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X1 ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('109',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('112',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_lattice3 @ X18 @ X19 @ X20 )
      | ( r2_lattice3 @ X18 @ X19 @ ( sk_D_1 @ X20 @ X19 @ X18 ) )
      | ( X20
        = ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( r2_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( r2_lattice3 @ sk_A @ X1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['109','117'])).

thf('119',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('123',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_lattice3 @ X18 @ X19 @ X20 )
      | ( m1_subset_1 @ ( sk_D_1 @ X20 @ X19 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ( X20
        = ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_lattice3 @ X23 @ ( k1_tarski @ X24 ) @ X22 )
      | ( r1_orders_2 @ X23 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('132',plain,(
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
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
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
    inference('sup-',[status(thm)],['119','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','136'])).

thf('138',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( r1_orders_2 @ X18 @ X20 @ ( sk_D_1 @ X20 @ X19 @ X18 ) )
      | ( X20
        = ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('140',plain,
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
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
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
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','143'])).

thf('145',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','145'])).

thf('147',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','147'])).

thf('149',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('151',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X29 ) @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X7: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('154',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('156',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_tarski @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['149','160'])).

thf('162',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_lattice3 @ X23 @ ( k1_tarski @ X24 ) @ X22 )
      | ( r1_orders_2 @ X23 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['65','168'])).

thf('170',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('172',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
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
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('175',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('176',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('178',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WgMuDL9IY6
% 0.13/0.36  % Computer   : n009.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:57:41 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.39/1.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.39/1.63  % Solved by: fo/fo7.sh
% 1.39/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.63  % done 723 iterations in 1.149s
% 1.39/1.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.39/1.63  % SZS output start Refutation
% 1.39/1.63  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 1.39/1.63  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 1.39/1.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.39/1.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.39/1.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.39/1.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.39/1.63  thf(sk_C_type, type, sk_C: $i).
% 1.39/1.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.39/1.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.39/1.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.39/1.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.39/1.63  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.39/1.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.39/1.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.39/1.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.39/1.63  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 1.39/1.63  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.39/1.63  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 1.39/1.63  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 1.39/1.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.39/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.39/1.63  thf(sk_E_type, type, sk_E: $i > $i).
% 1.39/1.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.39/1.63  thf(sk_B_type, type, sk_B: $i).
% 1.39/1.63  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 1.39/1.63  thf(t52_waybel_0, conjecture,
% 1.39/1.63    (![A:$i]:
% 1.39/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.39/1.63         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.39/1.63       ( ![B:$i]:
% 1.39/1.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.63           ( ![C:$i]:
% 1.39/1.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.63               ( ( ( ![D:$i]:
% 1.39/1.63                     ( ( ( v1_finset_1 @ D ) & 
% 1.39/1.63                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 1.39/1.63                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 1.39/1.63                         ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 1.39/1.63                   ( ![D:$i]:
% 1.39/1.63                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63                       ( ~( ( r2_hidden @ D @ C ) & 
% 1.39/1.63                            ( ![E:$i]:
% 1.39/1.63                              ( ( ( v1_finset_1 @ E ) & 
% 1.39/1.63                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 1.39/1.63                                ( ~( ( r1_yellow_0 @ A @ E ) & 
% 1.39/1.63                                     ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 1.39/1.63                   ( ![D:$i]:
% 1.39/1.63                     ( ( ( v1_finset_1 @ D ) & 
% 1.39/1.63                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 1.39/1.63                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 1.39/1.63                         ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 1.39/1.63                 ( ![D:$i]:
% 1.39/1.63                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63                     ( ( r2_lattice3 @ A @ B @ D ) <=>
% 1.39/1.63                       ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.39/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.63    (~( ![A:$i]:
% 1.39/1.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.39/1.63            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.39/1.63          ( ![B:$i]:
% 1.39/1.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.63              ( ![C:$i]:
% 1.39/1.63                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.63                  ( ( ( ![D:$i]:
% 1.39/1.63                        ( ( ( v1_finset_1 @ D ) & 
% 1.39/1.63                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 1.39/1.63                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 1.39/1.63                            ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 1.39/1.63                      ( ![D:$i]:
% 1.39/1.63                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63                          ( ~( ( r2_hidden @ D @ C ) & 
% 1.39/1.63                               ( ![E:$i]:
% 1.39/1.63                                 ( ( ( v1_finset_1 @ E ) & 
% 1.39/1.63                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 1.39/1.63                                   ( ~( ( r1_yellow_0 @ A @ E ) & 
% 1.39/1.63                                        ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 1.39/1.63                      ( ![D:$i]:
% 1.39/1.63                        ( ( ( v1_finset_1 @ D ) & 
% 1.39/1.63                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 1.39/1.63                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 1.39/1.63                            ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 1.39/1.63                    ( ![D:$i]:
% 1.39/1.63                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63                        ( ( r2_lattice3 @ A @ B @ D ) <=>
% 1.39/1.63                          ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 1.39/1.63    inference('cnf.neg', [status(esa)], [t52_waybel_0])).
% 1.39/1.63  thf('0', plain,
% 1.39/1.63      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.63        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('1', plain,
% 1.39/1.63      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 1.39/1.63       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.63      inference('split', [status(esa)], ['0'])).
% 1.39/1.63  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf(d9_lattice3, axiom,
% 1.39/1.63    (![A:$i]:
% 1.39/1.63     ( ( l1_orders_2 @ A ) =>
% 1.39/1.63       ( ![B:$i,C:$i]:
% 1.39/1.63         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 1.39/1.63             ( ![D:$i]:
% 1.39/1.63               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 1.39/1.63  thf('3', plain,
% 1.39/1.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.39/1.63         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 1.39/1.63          | (r2_hidden @ (sk_D @ X14 @ X16 @ X15) @ X16)
% 1.39/1.63          | (r2_lattice3 @ X15 @ X16 @ X14)
% 1.39/1.63          | ~ (l1_orders_2 @ X15))),
% 1.39/1.63      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.39/1.63  thf('4', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         (~ (l1_orders_2 @ sk_A)
% 1.39/1.63          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 1.39/1.63      inference('sup-', [status(thm)], ['2', '3'])).
% 1.39/1.63  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('6', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 1.39/1.63      inference('demod', [status(thm)], ['4', '5'])).
% 1.39/1.63  thf('7', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('8', plain,
% 1.39/1.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.39/1.63         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 1.39/1.63          | (m1_subset_1 @ (sk_D @ X14 @ X16 @ X15) @ (u1_struct_0 @ X15))
% 1.39/1.63          | (r2_lattice3 @ X15 @ X16 @ X14)
% 1.39/1.63          | ~ (l1_orders_2 @ X15))),
% 1.39/1.63      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.39/1.63  thf('9', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         (~ (l1_orders_2 @ sk_A)
% 1.39/1.63          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.63      inference('sup-', [status(thm)], ['7', '8'])).
% 1.39/1.63  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('11', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.63      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.63  thf('12', plain,
% 1.39/1.63      (![X30 : $i]:
% 1.39/1.63         (((X30) = (k1_yellow_0 @ sk_A @ (sk_E @ X30)))
% 1.39/1.63          | ~ (r2_hidden @ X30 @ sk_C)
% 1.39/1.63          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('13', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 1.39/1.63          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 1.39/1.63              = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)))))),
% 1.39/1.63      inference('sup-', [status(thm)], ['11', '12'])).
% 1.39/1.63  thf('14', plain,
% 1.39/1.63      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.63        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 1.39/1.63            = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 1.39/1.63        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.63      inference('sup-', [status(thm)], ['6', '13'])).
% 1.39/1.63  thf('15', plain,
% 1.39/1.63      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 1.39/1.63          = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 1.39/1.63        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.63      inference('simplify', [status(thm)], ['14'])).
% 1.39/1.63  thf('16', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 1.39/1.63      inference('demod', [status(thm)], ['4', '5'])).
% 1.39/1.63  thf('17', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.63      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.63  thf('18', plain,
% 1.39/1.63      (![X30 : $i]:
% 1.39/1.63         ((m1_subset_1 @ (sk_E @ X30) @ (k1_zfmisc_1 @ sk_B))
% 1.39/1.63          | ~ (r2_hidden @ X30 @ sk_C)
% 1.39/1.63          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('19', plain,
% 1.39/1.63      (![X0 : $i]:
% 1.39/1.63         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.63          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 1.39/1.63          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.63             (k1_zfmisc_1 @ sk_B)))),
% 1.39/1.63      inference('sup-', [status(thm)], ['17', '18'])).
% 1.39/1.63  thf('20', plain,
% 1.39/1.63      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.63        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 1.39/1.63           (k1_zfmisc_1 @ sk_B))
% 1.39/1.63        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.63      inference('sup-', [status(thm)], ['16', '19'])).
% 1.39/1.63  thf('21', plain,
% 1.39/1.63      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 1.39/1.63         (k1_zfmisc_1 @ sk_B))
% 1.39/1.63        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.63      inference('simplify', [status(thm)], ['20'])).
% 1.39/1.63  thf(t3_subset, axiom,
% 1.39/1.63    (![A:$i,B:$i]:
% 1.39/1.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.39/1.63  thf('22', plain,
% 1.39/1.63      (![X4 : $i, X5 : $i]:
% 1.39/1.63         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 1.39/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.39/1.63  thf('23', plain,
% 1.39/1.63      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.63        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 1.39/1.63      inference('sup-', [status(thm)], ['21', '22'])).
% 1.39/1.63  thf('24', plain,
% 1.39/1.63      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.63        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf('25', plain,
% 1.39/1.63      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 1.39/1.63         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.63      inference('split', [status(esa)], ['24'])).
% 1.39/1.63  thf('26', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.63  thf(t9_yellow_0, axiom,
% 1.39/1.63    (![A:$i]:
% 1.39/1.63     ( ( l1_orders_2 @ A ) =>
% 1.39/1.63       ( ![B:$i,C:$i]:
% 1.39/1.63         ( ( r1_tarski @ B @ C ) =>
% 1.39/1.63           ( ![D:$i]:
% 1.39/1.63             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.63               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 1.39/1.63                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 1.39/1.63  thf('27', plain,
% 1.39/1.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.39/1.63         (~ (r1_tarski @ X25 @ X26)
% 1.39/1.63          | ~ (r2_lattice3 @ X27 @ X26 @ X28)
% 1.39/1.63          | (r2_lattice3 @ X27 @ X25 @ X28)
% 1.39/1.64          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 1.39/1.64          | ~ (l1_orders_2 @ X27))),
% 1.39/1.64      inference('cnf', [status(esa)], [t9_yellow_0])).
% 1.39/1.64  thf('28', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         (~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 1.39/1.64          | ~ (r1_tarski @ X0 @ X1))),
% 1.39/1.64      inference('sup-', [status(thm)], ['26', '27'])).
% 1.39/1.64  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('30', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 1.39/1.64          | ~ (r1_tarski @ X0 @ X1))),
% 1.39/1.64      inference('demod', [status(thm)], ['28', '29'])).
% 1.39/1.64  thf('31', plain,
% 1.39/1.64      ((![X0 : $i]:
% 1.39/1.64          (~ (r1_tarski @ X0 @ sk_B) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['25', '30'])).
% 1.39/1.64  thf('32', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 1.39/1.64            sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['23', '31'])).
% 1.39/1.64  thf('33', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 1.39/1.64      inference('demod', [status(thm)], ['4', '5'])).
% 1.39/1.64  thf('34', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('35', plain,
% 1.39/1.64      (![X30 : $i]:
% 1.39/1.64         ((r1_yellow_0 @ sk_A @ (sk_E @ X30))
% 1.39/1.64          | ~ (r2_hidden @ X30 @ sk_C)
% 1.39/1.64          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('36', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 1.39/1.64          | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 1.39/1.64      inference('sup-', [status(thm)], ['34', '35'])).
% 1.39/1.64  thf('37', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64        | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['33', '36'])).
% 1.39/1.64  thf('38', plain,
% 1.39/1.64      (((r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['37'])).
% 1.39/1.64  thf('39', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('40', plain,
% 1.39/1.64      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 1.39/1.64          = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['14'])).
% 1.39/1.64  thf(d9_yellow_0, axiom,
% 1.39/1.64    (![A:$i]:
% 1.39/1.64     ( ( l1_orders_2 @ A ) =>
% 1.39/1.64       ( ![B:$i,C:$i]:
% 1.39/1.64         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.64           ( ( r1_yellow_0 @ A @ B ) =>
% 1.39/1.64             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 1.39/1.64               ( ( r2_lattice3 @ A @ B @ C ) & 
% 1.39/1.64                 ( ![D:$i]:
% 1.39/1.64                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.64                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 1.39/1.64                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.39/1.64  thf('41', plain,
% 1.39/1.64      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.39/1.64         (((X20) != (k1_yellow_0 @ X18 @ X19))
% 1.39/1.64          | ~ (r2_lattice3 @ X18 @ X19 @ X21)
% 1.39/1.64          | (r1_orders_2 @ X18 @ X20 @ X21)
% 1.39/1.64          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 1.39/1.64          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 1.39/1.64          | ~ (r1_yellow_0 @ X18 @ X19)
% 1.39/1.64          | ~ (l1_orders_2 @ X18))),
% 1.39/1.64      inference('cnf', [status(esa)], [d9_yellow_0])).
% 1.39/1.64  thf('42', plain,
% 1.39/1.64      (![X18 : $i, X19 : $i, X21 : $i]:
% 1.39/1.64         (~ (l1_orders_2 @ X18)
% 1.39/1.64          | ~ (r1_yellow_0 @ X18 @ X19)
% 1.39/1.64          | ~ (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 1.39/1.64          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 1.39/1.64          | (r1_orders_2 @ X18 @ (k1_yellow_0 @ X18 @ X19) @ X21)
% 1.39/1.64          | ~ (r2_lattice3 @ X18 @ X19 @ X21))),
% 1.39/1.64      inference('simplify', [status(thm)], ['41'])).
% 1.39/1.64  thf('43', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['40', '42'])).
% 1.39/1.64  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('45', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 1.39/1.64      inference('demod', [status(thm)], ['43', '44'])).
% 1.39/1.64  thf('46', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['39', '45'])).
% 1.39/1.64  thf('47', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['46'])).
% 1.39/1.64  thf('48', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0))),
% 1.39/1.64      inference('sup-', [status(thm)], ['38', '47'])).
% 1.39/1.64  thf('49', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ X0)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['48'])).
% 1.39/1.64  thf('50', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 1.39/1.64         | (r1_orders_2 @ sk_A @ 
% 1.39/1.64            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 1.39/1.64            sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['32', '49'])).
% 1.39/1.64  thf('51', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('52', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | (r1_orders_2 @ sk_A @ 
% 1.39/1.64            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 1.39/1.64            sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('demod', [status(thm)], ['50', '51'])).
% 1.39/1.64  thf('53', plain,
% 1.39/1.64      ((((r1_orders_2 @ sk_A @ 
% 1.39/1.64          (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 1.39/1.64          sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['52'])).
% 1.39/1.64  thf('54', plain,
% 1.39/1.64      ((((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('sup+', [status(thm)], ['15', '53'])).
% 1.39/1.64  thf('55', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 1.39/1.64         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['54'])).
% 1.39/1.64  thf('56', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('57', plain,
% 1.39/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 1.39/1.64          | ~ (r1_orders_2 @ X15 @ (sk_D @ X14 @ X16 @ X15) @ X14)
% 1.39/1.64          | (r2_lattice3 @ X15 @ X16 @ X14)
% 1.39/1.64          | ~ (l1_orders_2 @ X15))),
% 1.39/1.64      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.39/1.64  thf('58', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['56', '57'])).
% 1.39/1.64  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('60', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 1.39/1.64      inference('demod', [status(thm)], ['58', '59'])).
% 1.39/1.64  thf('61', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('clc', [status(thm)], ['55', '60'])).
% 1.39/1.64  thf('62', plain,
% 1.39/1.64      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 1.39/1.64         <= (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('split', [status(esa)], ['0'])).
% 1.39/1.64  thf('63', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 1.39/1.64       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['61', '62'])).
% 1.39/1.64  thf('64', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 1.39/1.64       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('split', [status(esa)], ['24'])).
% 1.39/1.64  thf('65', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('66', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 1.39/1.64      inference('demod', [status(thm)], ['4', '5'])).
% 1.39/1.64  thf(l1_zfmisc_1, axiom,
% 1.39/1.64    (![A:$i,B:$i]:
% 1.39/1.64     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.39/1.64  thf('67', plain,
% 1.39/1.64      (![X1 : $i, X3 : $i]:
% 1.39/1.64         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 1.39/1.64      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.39/1.64  thf('68', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r1_tarski @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ X0))),
% 1.39/1.64      inference('sup-', [status(thm)], ['66', '67'])).
% 1.39/1.64  thf('69', plain,
% 1.39/1.64      (![X4 : $i, X6 : $i]:
% 1.39/1.64         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 1.39/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.39/1.64  thf('70', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (k1_zfmisc_1 @ X0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['68', '69'])).
% 1.39/1.64  thf('71', plain,
% 1.39/1.64      (![X31 : $i]:
% 1.39/1.64         (((X31) = (k1_xboole_0))
% 1.39/1.64          | (r1_yellow_0 @ sk_A @ X31)
% 1.39/1.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ sk_B))
% 1.39/1.64          | ~ (v1_finset_1 @ X31))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('72', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['70', '71'])).
% 1.39/1.64  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 1.39/1.64  thf('73', plain, (![X7 : $i]: (v1_finset_1 @ (k1_tarski @ X7))),
% 1.39/1.64      inference('cnf', [status(esa)], [fc1_finset_1])).
% 1.39/1.64  thf('74', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('demod', [status(thm)], ['72', '73'])).
% 1.39/1.64  thf('75', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('76', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('77', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('78', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf(reflexivity_r3_orders_2, axiom,
% 1.39/1.64    (![A:$i,B:$i,C:$i]:
% 1.39/1.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.39/1.64         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.39/1.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.64       ( r3_orders_2 @ A @ B @ B ) ))).
% 1.39/1.64  thf('79', plain,
% 1.39/1.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.39/1.64         ((r3_orders_2 @ X11 @ X12 @ X12)
% 1.39/1.64          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 1.39/1.64          | ~ (l1_orders_2 @ X11)
% 1.39/1.64          | ~ (v3_orders_2 @ X11)
% 1.39/1.64          | (v2_struct_0 @ X11)
% 1.39/1.64          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11)))),
% 1.39/1.64      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 1.39/1.64  thf('80', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | ~ (v3_orders_2 @ sk_A)
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['78', '79'])).
% 1.39/1.64  thf('81', plain, ((v3_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('83', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.39/1.64  thf('84', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['77', '83'])).
% 1.39/1.64  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('86', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('clc', [status(thm)], ['84', '85'])).
% 1.39/1.64  thf('87', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf(redefinition_r3_orders_2, axiom,
% 1.39/1.64    (![A:$i,B:$i,C:$i]:
% 1.39/1.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.39/1.64         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.39/1.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.64       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 1.39/1.64  thf('88', plain,
% 1.39/1.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 1.39/1.64          | ~ (l1_orders_2 @ X9)
% 1.39/1.64          | ~ (v3_orders_2 @ X9)
% 1.39/1.64          | (v2_struct_0 @ X9)
% 1.39/1.64          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 1.39/1.64          | (r1_orders_2 @ X9 @ X8 @ X10)
% 1.39/1.64          | ~ (r3_orders_2 @ X9 @ X8 @ X10))),
% 1.39/1.64      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 1.39/1.64  thf('89', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 1.39/1.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | ~ (v3_orders_2 @ sk_A)
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A))),
% 1.39/1.64      inference('sup-', [status(thm)], ['87', '88'])).
% 1.39/1.64  thf('90', plain, ((v3_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('92', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r3_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 1.39/1.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A))),
% 1.39/1.64      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.39/1.64  thf('93', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['86', '92'])).
% 1.39/1.64  thf('94', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['93'])).
% 1.39/1.64  thf('95', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['76', '94'])).
% 1.39/1.64  thf('96', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64           (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | (v2_struct_0 @ sk_A)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['95'])).
% 1.39/1.64  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('98', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('clc', [status(thm)], ['96', '97'])).
% 1.39/1.64  thf('99', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf(t7_yellow_0, axiom,
% 1.39/1.64    (![A:$i]:
% 1.39/1.64     ( ( l1_orders_2 @ A ) =>
% 1.39/1.64       ( ![B:$i]:
% 1.39/1.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.64           ( ![C:$i]:
% 1.39/1.64             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.39/1.64               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 1.39/1.64                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 1.39/1.64                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 1.39/1.64                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 1.39/1.64                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 1.39/1.64                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 1.39/1.64                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 1.39/1.64                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 1.39/1.64  thf('100', plain,
% 1.39/1.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 1.39/1.64          | ~ (r1_orders_2 @ X23 @ X24 @ X22)
% 1.39/1.64          | (r2_lattice3 @ X23 @ (k1_tarski @ X24) @ X22)
% 1.39/1.64          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 1.39/1.64          | ~ (l1_orders_2 @ X23))),
% 1.39/1.64      inference('cnf', [status(esa)], [t7_yellow_0])).
% 1.39/1.64  thf('101', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['99', '100'])).
% 1.39/1.64  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('103', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ X1) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['101', '102'])).
% 1.39/1.64  thf('104', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['98', '103'])).
% 1.39/1.64  thf('105', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['104'])).
% 1.39/1.64  thf('106', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('107', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('clc', [status(thm)], ['105', '106'])).
% 1.39/1.64  thf('108', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('109', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('demod', [status(thm)], ['72', '73'])).
% 1.39/1.64  thf('110', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('clc', [status(thm)], ['105', '106'])).
% 1.39/1.64  thf('111', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('112', plain,
% 1.39/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.39/1.64         (~ (r2_lattice3 @ X18 @ X19 @ X20)
% 1.39/1.64          | (r2_lattice3 @ X18 @ X19 @ (sk_D_1 @ X20 @ X19 @ X18))
% 1.39/1.64          | ((X20) = (k1_yellow_0 @ X18 @ X19))
% 1.39/1.64          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 1.39/1.64          | ~ (r1_yellow_0 @ X18 @ X19)
% 1.39/1.64          | ~ (l1_orders_2 @ X18))),
% 1.39/1.64      inference('cnf', [status(esa)], [d9_yellow_0])).
% 1.39/1.64  thf('113', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ X1)
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X1 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['111', '112'])).
% 1.39/1.64  thf('114', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('115', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ X1)
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X1 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A))
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['113', '114'])).
% 1.39/1.64  thf('116', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 1.39/1.64              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['110', '115'])).
% 1.39/1.64  thf('117', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 1.39/1.64              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['116'])).
% 1.39/1.64  thf('118', plain,
% 1.39/1.64      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 1.39/1.64      inference('sup-', [status(thm)], ['109', '117'])).
% 1.39/1.64  thf('119', plain,
% 1.39/1.64      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['118'])).
% 1.39/1.64  thf('120', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('demod', [status(thm)], ['72', '73'])).
% 1.39/1.64  thf('121', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('clc', [status(thm)], ['105', '106'])).
% 1.39/1.64  thf('122', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.64  thf('123', plain,
% 1.39/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.39/1.64         (~ (r2_lattice3 @ X18 @ X19 @ X20)
% 1.39/1.64          | (m1_subset_1 @ (sk_D_1 @ X20 @ X19 @ X18) @ (u1_struct_0 @ X18))
% 1.39/1.64          | ((X20) = (k1_yellow_0 @ X18 @ X19))
% 1.39/1.64          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 1.39/1.64          | ~ (r1_yellow_0 @ X18 @ X19)
% 1.39/1.64          | ~ (l1_orders_2 @ X18))),
% 1.39/1.64      inference('cnf', [status(esa)], [d9_yellow_0])).
% 1.39/1.64  thf('124', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ X1)
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 1.39/1.64          | (m1_subset_1 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 1.39/1.64             (u1_struct_0 @ sk_A))
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['122', '123'])).
% 1.39/1.64  thf('125', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('126', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ X1)
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A) = (k1_yellow_0 @ sk_A @ X1))
% 1.39/1.64          | (m1_subset_1 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1 @ sk_A) @ 
% 1.39/1.64             (u1_struct_0 @ sk_A))
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['124', '125'])).
% 1.39/1.64  thf('127', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 1.39/1.64             (u1_struct_0 @ sk_A))
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 1.39/1.64              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 1.39/1.64          | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['121', '126'])).
% 1.39/1.64  thf('128', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)))
% 1.39/1.64          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 1.39/1.64              = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A))))
% 1.39/1.64          | (m1_subset_1 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ 
% 1.39/1.64              (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ sk_A) @ 
% 1.39/1.64             (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['127'])).
% 1.39/1.64  thf('129', plain,
% 1.39/1.64      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (m1_subset_1 @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 1.39/1.64           (u1_struct_0 @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 1.39/1.64      inference('sup-', [status(thm)], ['120', '128'])).
% 1.39/1.64  thf('130', plain,
% 1.39/1.64      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (m1_subset_1 @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A) @ 
% 1.39/1.64           (u1_struct_0 @ sk_A))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['129'])).
% 1.39/1.64  thf('131', plain,
% 1.39/1.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 1.39/1.64          | ~ (r2_lattice3 @ X23 @ (k1_tarski @ X24) @ X22)
% 1.39/1.64          | (r1_orders_2 @ X23 @ X24 @ X22)
% 1.39/1.64          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 1.39/1.64          | ~ (l1_orders_2 @ X23))),
% 1.39/1.64      inference('cnf', [status(esa)], [t7_yellow_0])).
% 1.39/1.64  thf('132', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64              = (k1_yellow_0 @ sk_A @ 
% 1.39/1.64                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64          | ~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ X0 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 1.39/1.64               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['130', '131'])).
% 1.39/1.64  thf('133', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('134', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64          | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64          | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64              = (k1_yellow_0 @ sk_A @ 
% 1.39/1.64                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ X0 @ 
% 1.39/1.64             (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64              (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ 
% 1.39/1.64               (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['132', '133'])).
% 1.39/1.64  thf('135', plain,
% 1.39/1.64      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['119', '134'])).
% 1.39/1.64  thf('136', plain,
% 1.39/1.64      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['135'])).
% 1.39/1.64  thf('137', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64           (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64            (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['108', '136'])).
% 1.39/1.64  thf('138', plain,
% 1.39/1.64      (((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64         (sk_D_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64          (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['137'])).
% 1.39/1.64  thf('139', plain,
% 1.39/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.39/1.64         (~ (r2_lattice3 @ X18 @ X19 @ X20)
% 1.39/1.64          | ~ (r1_orders_2 @ X18 @ X20 @ (sk_D_1 @ X20 @ X19 @ X18))
% 1.39/1.64          | ((X20) = (k1_yellow_0 @ X18 @ X19))
% 1.39/1.64          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 1.39/1.64          | ~ (r1_yellow_0 @ X18 @ X19)
% 1.39/1.64          | ~ (l1_orders_2 @ X18))),
% 1.39/1.64      inference('cnf', [status(esa)], [d9_yellow_0])).
% 1.39/1.64  thf('140', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ~ (l1_orders_2 @ sk_A)
% 1.39/1.64        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ~ (r2_lattice3 @ sk_A @ 
% 1.39/1.64             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['138', '139'])).
% 1.39/1.64  thf('141', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('142', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ~ (r2_lattice3 @ sk_A @ 
% 1.39/1.64             (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64             (sk_D @ sk_D_2 @ sk_B @ sk_A)))),
% 1.39/1.64      inference('demod', [status(thm)], ['140', '141'])).
% 1.39/1.64  thf('143', plain,
% 1.39/1.64      ((~ (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64           (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 1.39/1.64        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['142'])).
% 1.39/1.64  thf('144', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['107', '143'])).
% 1.39/1.64  thf('145', plain,
% 1.39/1.64      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.39/1.64        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['144'])).
% 1.39/1.64  thf('146', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))),
% 1.39/1.64      inference('sup-', [status(thm)], ['75', '145'])).
% 1.39/1.64  thf('147', plain,
% 1.39/1.64      ((~ (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('simplify', [status(thm)], ['146'])).
% 1.39/1.64  thf('148', plain,
% 1.39/1.64      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | ((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64            = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 1.39/1.64      inference('sup-', [status(thm)], ['74', '147'])).
% 1.39/1.64  thf('149', plain,
% 1.39/1.64      ((((sk_D @ sk_D_2 @ sk_B @ sk_A)
% 1.39/1.64          = (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['148'])).
% 1.39/1.64  thf('150', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 1.39/1.64             (k1_zfmisc_1 @ X0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['68', '69'])).
% 1.39/1.64  thf('151', plain,
% 1.39/1.64      (![X29 : $i]:
% 1.39/1.64         (((X29) = (k1_xboole_0))
% 1.39/1.64          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X29) @ sk_C)
% 1.39/1.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ sk_B))
% 1.39/1.64          | ~ (v1_finset_1 @ X29))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('152', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 1.39/1.64        | (r2_hidden @ 
% 1.39/1.64           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 1.39/1.64           sk_C)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['150', '151'])).
% 1.39/1.64  thf('153', plain, (![X7 : $i]: (v1_finset_1 @ (k1_tarski @ X7))),
% 1.39/1.64      inference('cnf', [status(esa)], [fc1_finset_1])).
% 1.39/1.64  thf('154', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r2_hidden @ 
% 1.39/1.64           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 1.39/1.64           sk_C)
% 1.39/1.64        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 1.39/1.64      inference('demod', [status(thm)], ['152', '153'])).
% 1.39/1.64  thf('155', plain,
% 1.39/1.64      (![X1 : $i, X3 : $i]:
% 1.39/1.64         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 1.39/1.64      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.39/1.64  thf('156', plain,
% 1.39/1.64      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64        | (r1_tarski @ 
% 1.39/1.64           (k1_tarski @ 
% 1.39/1.64            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 1.39/1.64           sk_C))),
% 1.39/1.64      inference('sup-', [status(thm)], ['154', '155'])).
% 1.39/1.64  thf('157', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('split', [status(esa)], ['24'])).
% 1.39/1.64  thf('158', plain,
% 1.39/1.64      (![X0 : $i, X1 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 1.39/1.64          | ~ (r1_tarski @ X0 @ X1))),
% 1.39/1.64      inference('demod', [status(thm)], ['28', '29'])).
% 1.39/1.64  thf('159', plain,
% 1.39/1.64      ((![X0 : $i]:
% 1.39/1.64          (~ (r1_tarski @ X0 @ sk_C) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['157', '158'])).
% 1.39/1.64  thf('160', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64         | (r2_lattice3 @ sk_A @ 
% 1.39/1.64            (k1_tarski @ 
% 1.39/1.64             (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 1.39/1.64            sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['156', '159'])).
% 1.39/1.64  thf('161', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64          sk_D_2)
% 1.39/1.64         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('sup+', [status(thm)], ['149', '160'])).
% 1.39/1.64  thf('162', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64         | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 1.39/1.64            sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['161'])).
% 1.39/1.64  thf('163', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('164', plain,
% 1.39/1.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 1.39/1.64          | ~ (r2_lattice3 @ X23 @ (k1_tarski @ X24) @ X22)
% 1.39/1.64          | (r1_orders_2 @ X23 @ X24 @ X22)
% 1.39/1.64          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 1.39/1.64          | ~ (l1_orders_2 @ X23))),
% 1.39/1.64      inference('cnf', [status(esa)], [t7_yellow_0])).
% 1.39/1.64  thf('165', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (l1_orders_2 @ sk_A)
% 1.39/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['163', '164'])).
% 1.39/1.64  thf('166', plain, ((l1_orders_2 @ sk_A)),
% 1.39/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.64  thf('167', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.39/1.64          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 1.39/1.64      inference('demod', [status(thm)], ['165', '166'])).
% 1.39/1.64  thf('168', plain,
% 1.39/1.64      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 1.39/1.64         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 1.39/1.64              (u1_struct_0 @ sk_A))))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['162', '167'])).
% 1.39/1.64  thf('169', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['65', '168'])).
% 1.39/1.64  thf('170', plain,
% 1.39/1.64      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 1.39/1.64         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 1.39/1.64         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('simplify', [status(thm)], ['169'])).
% 1.39/1.64  thf('171', plain,
% 1.39/1.64      (![X0 : $i]:
% 1.39/1.64         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 1.39/1.64          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 1.39/1.64      inference('demod', [status(thm)], ['58', '59'])).
% 1.39/1.64  thf('172', plain,
% 1.39/1.64      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 1.39/1.64         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('clc', [status(thm)], ['170', '171'])).
% 1.39/1.64  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 1.39/1.64  thf('173', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 1.39/1.64      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.39/1.64  thf('174', plain,
% 1.39/1.64      (((~ (v1_xboole_0 @ k1_xboole_0) | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('sup-', [status(thm)], ['172', '173'])).
% 1.39/1.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.39/1.64  thf('175', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.39/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.39/1.64  thf('176', plain,
% 1.39/1.64      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 1.39/1.64         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 1.39/1.64      inference('demod', [status(thm)], ['174', '175'])).
% 1.39/1.64  thf('177', plain,
% 1.39/1.64      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 1.39/1.64         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 1.39/1.64      inference('split', [status(esa)], ['0'])).
% 1.39/1.64  thf('178', plain,
% 1.39/1.64      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 1.39/1.64       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 1.39/1.64      inference('sup-', [status(thm)], ['176', '177'])).
% 1.39/1.64  thf('179', plain, ($false),
% 1.39/1.64      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '178'])).
% 1.39/1.64  
% 1.39/1.64  % SZS output end Refutation
% 1.39/1.64  
% 1.39/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
