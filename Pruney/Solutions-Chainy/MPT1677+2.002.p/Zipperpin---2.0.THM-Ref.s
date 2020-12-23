%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ta8CQZMcbR

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:46 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 294 expanded)
%              Number of leaves         :   37 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          : 1870 (9029 expanded)
%              Number of equality atoms :   30 ( 289 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
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
    ! [X32: $i] :
      ( ( X32
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X32 ) ) )
      | ~ ( r2_hidden @ X32 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_C )
      | ( X32
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X32 ) ) ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X32 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X32 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ X32 ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_lattice3 @ X29 @ X28 @ X30 )
      | ( r1_lattice3 @ X29 @ X27 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

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

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k2_yellow_0 @ X14 @ X15 ) )
      | ~ ( r1_lattice3 @ X14 @ X15 @ X17 )
      | ( r1_orders_2 @ X14 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X17 @ ( k2_yellow_0 @ X14 @ X15 ) )
      | ~ ( r1_lattice3 @ X14 @ X15 @ X17 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X32: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( sk_E @ X32 ) )
      | ~ ( r2_hidden @ X32 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['38','48'])).

thf('50',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['12','49'])).

thf('51',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X10 @ ( sk_D @ X10 @ X12 @ X11 ) )
      | ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['51','56'])).

thf('58',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_yellow_0 @ sk_A @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('67',plain,(
    ! [X9: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('68',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16
       != ( k2_yellow_0 @ X14 @ X15 ) )
      | ( r1_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattice3 @ X14 @ X15 @ ( k2_yellow_0 @ X14 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('78',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X31 ) @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X9: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('81',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ sk_C ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['81','92'])).

thf('94',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(t12_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ D @ C ) )
               => ( r1_lattice3 @ A @ B @ D ) ) ) ) ) )).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_lattice3 @ X21 @ X22 @ X20 )
      | ~ ( r1_orders_2 @ X21 @ X23 @ X20 )
      | ( r1_lattice3 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattice3 @ X0 @ X3 @ X2 )
      | ~ ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['76','102'])).

thf('104',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('106',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_lattice3 @ X25 @ ( k1_tarski @ X26 ) @ X24 )
      | ( r1_orders_2 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','110'])).

thf('112',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('114',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('115',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('116',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('117',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('118',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','59','60','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ta8CQZMcbR
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.83/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.03  % Solved by: fo/fo7.sh
% 0.83/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.03  % done 403 iterations in 0.604s
% 0.83/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.03  % SZS output start Refutation
% 0.83/1.03  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.83/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.03  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.83/1.03  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.83/1.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.03  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.83/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.03  thf(sk_E_type, type, sk_E: $i > $i).
% 0.83/1.03  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.83/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.03  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.83/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.83/1.03  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.83/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.03  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.83/1.03  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.83/1.03  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.83/1.03  thf(t57_waybel_0, conjecture,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.83/1.03         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03           ( ![C:$i]:
% 0.83/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03               ( ( ( ![D:$i]:
% 0.83/1.03                     ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.03                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.03                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.03                         ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.83/1.03                   ( ![D:$i]:
% 0.83/1.03                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.83/1.03                            ( ![E:$i]:
% 0.83/1.03                              ( ( ( v1_finset_1 @ E ) & 
% 0.83/1.03                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.03                                ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.83/1.03                                     ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.83/1.03                   ( ![D:$i]:
% 0.83/1.03                     ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.03                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.03                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.03                         ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.83/1.03                 ( ![D:$i]:
% 0.83/1.03                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03                     ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.83/1.03                       ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.03    (~( ![A:$i]:
% 0.83/1.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.83/1.03            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.83/1.03          ( ![B:$i]:
% 0.83/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03              ( ![C:$i]:
% 0.83/1.03                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03                  ( ( ( ![D:$i]:
% 0.83/1.03                        ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.03                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.03                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.03                            ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.83/1.03                      ( ![D:$i]:
% 0.83/1.03                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.83/1.03                               ( ![E:$i]:
% 0.83/1.03                                 ( ( ( v1_finset_1 @ E ) & 
% 0.83/1.03                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.03                                   ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.83/1.03                                        ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.83/1.03                      ( ![D:$i]:
% 0.83/1.03                        ( ( ( v1_finset_1 @ D ) & 
% 0.83/1.03                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.83/1.03                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.83/1.03                            ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.83/1.03                    ( ![D:$i]:
% 0.83/1.03                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03                        ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.83/1.03                          ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.83/1.03    inference('cnf.neg', [status(esa)], [t57_waybel_0])).
% 0.83/1.03  thf('0', plain,
% 0.83/1.03      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03        | ~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('1', plain,
% 0.83/1.03      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.03       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.03      inference('split', [status(esa)], ['0'])).
% 0.83/1.03  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(d8_lattice3, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( l1_orders_2 @ A ) =>
% 0.83/1.03       ( ![B:$i,C:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.83/1.03             ( ![D:$i]:
% 0.83/1.03               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.83/1.03  thf('3', plain,
% 0.83/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.83/1.03          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.83/1.03          | (r1_lattice3 @ X11 @ X12 @ X10)
% 0.83/1.03          | ~ (l1_orders_2 @ X11))),
% 0.83/1.03      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.03  thf('4', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.83/1.03  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('6', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('7', plain,
% 0.83/1.03      (![X32 : $i]:
% 0.83/1.03         (((X32) = (k2_yellow_0 @ sk_A @ (sk_E @ X32)))
% 0.83/1.03          | ~ (r2_hidden @ X32 @ sk_C)
% 0.83/1.03          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('8', plain,
% 0.83/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(t4_subset, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.83/1.03       ( m1_subset_1 @ A @ C ) ))).
% 0.83/1.03  thf('9', plain,
% 0.83/1.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.03         (~ (r2_hidden @ X6 @ X7)
% 0.83/1.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.83/1.03          | (m1_subset_1 @ X6 @ X8))),
% 0.83/1.03      inference('cnf', [status(esa)], [t4_subset])).
% 0.83/1.03  thf('10', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.83/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.03  thf('11', plain,
% 0.83/1.03      (![X32 : $i]:
% 0.83/1.03         (~ (r2_hidden @ X32 @ sk_C)
% 0.83/1.03          | ((X32) = (k2_yellow_0 @ sk_A @ (sk_E @ X32))))),
% 0.83/1.03      inference('clc', [status(thm)], ['7', '10'])).
% 0.83/1.03  thf('12', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.83/1.03            = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['6', '11'])).
% 0.83/1.03  thf('13', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('14', plain,
% 0.83/1.03      (![X32 : $i]:
% 0.83/1.03         ((m1_subset_1 @ (sk_E @ X32) @ (k1_zfmisc_1 @ sk_B))
% 0.83/1.03          | ~ (r2_hidden @ X32 @ sk_C)
% 0.83/1.03          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('15', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.83/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.03  thf('16', plain,
% 0.83/1.03      (![X32 : $i]:
% 0.83/1.03         (~ (r2_hidden @ X32 @ sk_C)
% 0.83/1.03          | (m1_subset_1 @ (sk_E @ X32) @ (k1_zfmisc_1 @ sk_B)))),
% 0.83/1.03      inference('clc', [status(thm)], ['14', '15'])).
% 0.83/1.03  thf('17', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.83/1.03           (k1_zfmisc_1 @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['13', '16'])).
% 0.83/1.03  thf(t3_subset, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.03  thf('18', plain,
% 0.83/1.03      (![X3 : $i, X4 : $i]:
% 0.83/1.03         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.83/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.03  thf('19', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.83/1.03      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.03  thf('20', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('21', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('split', [status(esa)], ['20'])).
% 0.83/1.03  thf('22', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(t9_yellow_0, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( l1_orders_2 @ A ) =>
% 0.83/1.03       ( ![B:$i,C:$i]:
% 0.83/1.03         ( ( r1_tarski @ B @ C ) =>
% 0.83/1.03           ( ![D:$i]:
% 0.83/1.03             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.83/1.03                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.83/1.03  thf('23', plain,
% 0.83/1.03      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.83/1.03         (~ (r1_tarski @ X27 @ X28)
% 0.83/1.03          | ~ (r1_lattice3 @ X29 @ X28 @ X30)
% 0.83/1.03          | (r1_lattice3 @ X29 @ X27 @ X30)
% 0.83/1.03          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.83/1.03          | ~ (l1_orders_2 @ X29))),
% 0.83/1.03      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.83/1.03  thf('24', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.03          | ~ (r1_tarski @ X0 @ X1))),
% 0.83/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.83/1.03  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('26', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.03          | ~ (r1_tarski @ X0 @ X1))),
% 0.83/1.03      inference('demod', [status(thm)], ['24', '25'])).
% 0.83/1.03  thf('27', plain,
% 0.83/1.03      ((![X0 : $i]:
% 0.83/1.03          (~ (r1_tarski @ X0 @ sk_B) | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['21', '26'])).
% 0.83/1.03  thf('28', plain,
% 0.83/1.03      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03         | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.83/1.03            sk_D_2)))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['19', '27'])).
% 0.83/1.03  thf('29', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(dt_k2_yellow_0, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( l1_orders_2 @ A ) =>
% 0.83/1.03       ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.83/1.03  thf('30', plain,
% 0.83/1.03      (![X18 : $i, X19 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X18)
% 0.83/1.03          | (m1_subset_1 @ (k2_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.83/1.03  thf(d10_yellow_0, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( l1_orders_2 @ A ) =>
% 0.83/1.03       ( ![B:$i,C:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03           ( ( r2_yellow_0 @ A @ B ) =>
% 0.83/1.03             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.83/1.03               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.83/1.03                 ( ![D:$i]:
% 0.83/1.03                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.83/1.03                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.03  thf('31', plain,
% 0.83/1.03      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.83/1.03         (((X16) != (k2_yellow_0 @ X14 @ X15))
% 0.83/1.03          | ~ (r1_lattice3 @ X14 @ X15 @ X17)
% 0.83/1.03          | (r1_orders_2 @ X14 @ X17 @ X16)
% 0.83/1.03          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.83/1.03          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.83/1.03          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.83/1.03          | ~ (l1_orders_2 @ X14))),
% 0.83/1.03      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.83/1.03  thf('32', plain,
% 0.83/1.03      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X14)
% 0.83/1.03          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.83/1.03          | ~ (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14))
% 0.83/1.03          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.83/1.03          | (r1_orders_2 @ X14 @ X17 @ (k2_yellow_0 @ X14 @ X15))
% 0.83/1.03          | ~ (r1_lattice3 @ X14 @ X15 @ X17))),
% 0.83/1.03      inference('simplify', [status(thm)], ['31'])).
% 0.83/1.03  thf('33', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X0)
% 0.83/1.03          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.83/1.03          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.83/1.03          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.83/1.03          | ~ (l1_orders_2 @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['30', '32'])).
% 0.83/1.03  thf('34', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         (~ (r2_yellow_0 @ X0 @ X1)
% 0.83/1.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.83/1.03          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.83/1.03          | ~ (l1_orders_2 @ X0))),
% 0.83/1.03      inference('simplify', [status(thm)], ['33'])).
% 0.83/1.03  thf('35', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.83/1.03          | ~ (r2_yellow_0 @ sk_A @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['29', '34'])).
% 0.83/1.03  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('37', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.83/1.03          | ~ (r2_yellow_0 @ sk_A @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['35', '36'])).
% 0.83/1.03  thf('38', plain,
% 0.83/1.03      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03         | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.03         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.83/1.03            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['28', '37'])).
% 0.83/1.03  thf('39', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('40', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('41', plain,
% 0.83/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.83/1.03          | (m1_subset_1 @ (sk_D @ X10 @ X12 @ X11) @ (u1_struct_0 @ X11))
% 0.83/1.03          | (r1_lattice3 @ X11 @ X12 @ X10)
% 0.83/1.03          | ~ (l1_orders_2 @ X11))),
% 0.83/1.03      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.03  thf('42', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['40', '41'])).
% 0.83/1.03  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('44', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('demod', [status(thm)], ['42', '43'])).
% 0.83/1.03  thf('45', plain,
% 0.83/1.03      (![X32 : $i]:
% 0.83/1.03         ((r2_yellow_0 @ sk_A @ (sk_E @ X32))
% 0.83/1.03          | ~ (r2_hidden @ X32 @ sk_C)
% 0.83/1.03          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('46', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.83/1.03          | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.83/1.03  thf('47', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03        | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.03        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.03      inference('sup-', [status(thm)], ['39', '46'])).
% 0.83/1.03  thf('48', plain,
% 0.83/1.03      (((r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.83/1.03        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.83/1.03      inference('simplify', [status(thm)], ['47'])).
% 0.83/1.03  thf('49', plain,
% 0.83/1.03      ((((r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.83/1.03          (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.03         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('clc', [status(thm)], ['38', '48'])).
% 0.83/1.03  thf('50', plain,
% 0.83/1.03      ((((r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))
% 0.83/1.03         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['12', '49'])).
% 0.83/1.03  thf('51', plain,
% 0.83/1.03      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.83/1.03         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['50'])).
% 0.83/1.03  thf('52', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('53', plain,
% 0.83/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.83/1.03          | ~ (r1_orders_2 @ X11 @ X10 @ (sk_D @ X10 @ X12 @ X11))
% 0.83/1.03          | (r1_lattice3 @ X11 @ X12 @ X10)
% 0.83/1.03          | ~ (l1_orders_2 @ X11))),
% 0.83/1.03      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.03  thf('54', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['52', '53'])).
% 0.83/1.03  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('56', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.03      inference('demod', [status(thm)], ['54', '55'])).
% 0.83/1.03  thf('57', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.03      inference('clc', [status(thm)], ['51', '56'])).
% 0.83/1.03  thf('58', plain,
% 0.83/1.03      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.83/1.03         <= (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.03      inference('split', [status(esa)], ['0'])).
% 0.83/1.03  thf('59', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.03       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.03      inference('sup-', [status(thm)], ['57', '58'])).
% 0.83/1.03  thf('60', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.03       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.03      inference('split', [status(esa)], ['20'])).
% 0.83/1.03  thf('61', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('demod', [status(thm)], ['42', '43'])).
% 0.83/1.03  thf('62', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.83/1.03      inference('demod', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf(t63_subset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( r2_hidden @ A @ B ) =>
% 0.83/1.03       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.83/1.03  thf('63', plain,
% 0.83/1.03      (![X1 : $i, X2 : $i]:
% 0.83/1.03         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.83/1.03          | ~ (r2_hidden @ X1 @ X2))),
% 0.83/1.03      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.83/1.03  thf('64', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.03             (k1_zfmisc_1 @ X0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.83/1.03  thf('65', plain,
% 0.83/1.03      (![X33 : $i]:
% 0.83/1.03         (((X33) = (k1_xboole_0))
% 0.83/1.03          | (r2_yellow_0 @ sk_A @ X33)
% 0.83/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ sk_B))
% 0.83/1.03          | ~ (v1_finset_1 @ X33))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('66', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.03        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.03        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['64', '65'])).
% 0.83/1.03  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.83/1.03  thf('67', plain, (![X9 : $i]: (v1_finset_1 @ (k1_tarski @ X9))),
% 0.83/1.03      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.83/1.03  thf('68', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.03        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.03      inference('demod', [status(thm)], ['66', '67'])).
% 0.83/1.03  thf('69', plain,
% 0.83/1.03      (![X18 : $i, X19 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X18)
% 0.83/1.03          | (m1_subset_1 @ (k2_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.83/1.03  thf('70', plain,
% 0.83/1.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.03         (((X16) != (k2_yellow_0 @ X14 @ X15))
% 0.83/1.03          | (r1_lattice3 @ X14 @ X15 @ X16)
% 0.83/1.03          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.83/1.03          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.83/1.03          | ~ (l1_orders_2 @ X14))),
% 0.83/1.03      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.83/1.03  thf('71', plain,
% 0.83/1.03      (![X14 : $i, X15 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X14)
% 0.83/1.03          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.83/1.03          | ~ (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14))
% 0.83/1.03          | (r1_lattice3 @ X14 @ X15 @ (k2_yellow_0 @ X14 @ X15)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['70'])).
% 0.83/1.03  thf('72', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X0)
% 0.83/1.03          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.83/1.03          | ~ (l1_orders_2 @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['69', '71'])).
% 0.83/1.03  thf('73', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (r2_yellow_0 @ X0 @ X1)
% 0.83/1.03          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | ~ (l1_orders_2 @ X0))),
% 0.83/1.03      inference('simplify', [status(thm)], ['72'])).
% 0.83/1.03  thf('74', plain,
% 0.83/1.03      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.03        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03        | ~ (l1_orders_2 @ sk_A)
% 0.83/1.03        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.03           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['68', '73'])).
% 0.83/1.03  thf('75', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('76', plain,
% 0.83/1.03      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.03        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.03           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.83/1.03      inference('demod', [status(thm)], ['74', '75'])).
% 0.83/1.03  thf('77', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.83/1.03             (k1_zfmisc_1 @ X0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.83/1.03  thf('78', plain,
% 0.83/1.03      (![X31 : $i]:
% 0.83/1.03         (((X31) = (k1_xboole_0))
% 0.83/1.03          | (r2_hidden @ (k2_yellow_0 @ sk_A @ X31) @ sk_C)
% 0.83/1.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ sk_B))
% 0.83/1.03          | ~ (v1_finset_1 @ X31))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('79', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.83/1.03        | (r2_hidden @ 
% 0.83/1.03           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.83/1.03           sk_C)
% 0.83/1.03        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.83/1.03  thf('80', plain, (![X9 : $i]: (v1_finset_1 @ (k1_tarski @ X9))),
% 0.83/1.03      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.83/1.03  thf('81', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03        | (r2_hidden @ 
% 0.83/1.03           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.83/1.03           sk_C)
% 0.83/1.03        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.83/1.03      inference('demod', [status(thm)], ['79', '80'])).
% 0.83/1.03  thf('82', plain,
% 0.83/1.03      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.03      inference('split', [status(esa)], ['20'])).
% 0.83/1.03  thf('83', plain,
% 0.83/1.03      (![X18 : $i, X19 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X18)
% 0.83/1.03          | (m1_subset_1 @ (k2_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.83/1.03  thf('84', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('85', plain,
% 0.83/1.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.83/1.03          | ~ (r1_lattice3 @ X11 @ X12 @ X10)
% 0.83/1.03          | ~ (r2_hidden @ X13 @ X12)
% 0.83/1.03          | (r1_orders_2 @ X11 @ X10 @ X13)
% 0.83/1.03          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.83/1.03          | ~ (l1_orders_2 @ X11))),
% 0.83/1.03      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.83/1.03  thf('86', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.83/1.03          | ~ (r2_hidden @ X0 @ X1)
% 0.83/1.03          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.83/1.03      inference('sup-', [status(thm)], ['84', '85'])).
% 0.83/1.03  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('88', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.83/1.03          | ~ (r2_hidden @ X0 @ X1)
% 0.83/1.03          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.83/1.03      inference('demod', [status(thm)], ['86', '87'])).
% 0.83/1.03  thf('89', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ sk_A)
% 0.83/1.03          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.03          | ~ (r2_hidden @ (k2_yellow_0 @ sk_A @ X0) @ X1)
% 0.83/1.03          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['83', '88'])).
% 0.83/1.03  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('91', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.83/1.03          | ~ (r2_hidden @ (k2_yellow_0 @ sk_A @ X0) @ X1)
% 0.83/1.03          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.83/1.03      inference('demod', [status(thm)], ['89', '90'])).
% 0.83/1.03  thf('92', plain,
% 0.83/1.03      ((![X0 : $i]:
% 0.83/1.03          ((r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.83/1.03           | ~ (r2_hidden @ (k2_yellow_0 @ sk_A @ X0) @ sk_C)))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['82', '91'])).
% 0.83/1.03  thf('93', plain,
% 0.83/1.03      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.03         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.83/1.03            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.83/1.03         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['81', '92'])).
% 0.83/1.03  thf('94', plain,
% 0.83/1.03      (![X18 : $i, X19 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X18)
% 0.83/1.03          | (m1_subset_1 @ (k2_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.83/1.03  thf(t12_yellow_0, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.83/1.03       ( ![B:$i,C:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03           ( ![D:$i]:
% 0.83/1.03             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03               ( ( ( r1_lattice3 @ A @ B @ C ) & ( r1_orders_2 @ A @ D @ C ) ) =>
% 0.83/1.03                 ( r1_lattice3 @ A @ B @ D ) ) ) ) ) ) ))).
% 0.83/1.03  thf('95', plain,
% 0.83/1.03      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.83/1.03          | ~ (r1_lattice3 @ X21 @ X22 @ X20)
% 0.83/1.03          | ~ (r1_orders_2 @ X21 @ X23 @ X20)
% 0.83/1.03          | (r1_lattice3 @ X21 @ X22 @ X23)
% 0.83/1.03          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.83/1.03          | ~ (l1_orders_2 @ X21)
% 0.83/1.03          | ~ (v4_orders_2 @ X21))),
% 0.83/1.03      inference('cnf', [status(esa)], [t12_yellow_0])).
% 0.83/1.03  thf('96', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.03         (~ (l1_orders_2 @ X0)
% 0.83/1.03          | ~ (v4_orders_2 @ X0)
% 0.83/1.03          | ~ (l1_orders_2 @ X0)
% 0.83/1.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.83/1.03          | (r1_lattice3 @ X0 @ X3 @ X2)
% 0.83/1.03          | ~ (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['94', '95'])).
% 0.83/1.03  thf('97', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.03         (~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | ~ (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.83/1.03          | (r1_lattice3 @ X0 @ X3 @ X2)
% 0.83/1.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.83/1.03          | ~ (v4_orders_2 @ X0)
% 0.83/1.03          | ~ (l1_orders_2 @ X0))),
% 0.83/1.03      inference('simplify', [status(thm)], ['96'])).
% 0.83/1.03  thf('98', plain,
% 0.83/1.03      ((![X0 : $i]:
% 0.83/1.03          ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.03           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.03           | ~ (l1_orders_2 @ sk_A)
% 0.83/1.03           | ~ (v4_orders_2 @ sk_A)
% 0.83/1.03           | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.83/1.03           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.03           | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.83/1.03                (k2_yellow_0 @ sk_A @ 
% 0.83/1.04                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['93', '97'])).
% 0.83/1.04  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('100', plain, ((v4_orders_2 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('101', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('102', plain,
% 0.83/1.04      ((![X0 : $i]:
% 0.83/1.04          ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.04           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.04           | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.83/1.04                (k2_yellow_0 @ sk_A @ 
% 0.83/1.04                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.83/1.04  thf('103', plain,
% 0.83/1.04      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.04         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04         | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.04            sk_D_2)
% 0.83/1.04         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['76', '102'])).
% 0.83/1.04  thf('104', plain,
% 0.83/1.04      ((((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.83/1.04          sk_D_2)
% 0.83/1.04         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['103'])).
% 0.83/1.04  thf('105', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t7_yellow_0, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_orders_2 @ A ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.04           ( ![C:$i]:
% 0.83/1.04             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.04               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.83/1.04                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.83/1.04                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.83/1.04                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.83/1.04                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.83/1.04                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.83/1.04                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.83/1.04                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.83/1.04  thf('106', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.83/1.04          | ~ (r1_lattice3 @ X25 @ (k1_tarski @ X26) @ X24)
% 0.83/1.04          | (r1_orders_2 @ X25 @ X24 @ X26)
% 0.83/1.04          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.83/1.04          | ~ (l1_orders_2 @ X25))),
% 0.83/1.04      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.83/1.04  thf('107', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_orders_2 @ sk_A)
% 0.83/1.04          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.04          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.83/1.04          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.83/1.04      inference('sup-', [status(thm)], ['105', '106'])).
% 0.83/1.04  thf('108', plain, ((l1_orders_2 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('109', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.83/1.04          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.83/1.04          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.83/1.04      inference('demod', [status(thm)], ['107', '108'])).
% 0.83/1.04  thf('110', plain,
% 0.83/1.04      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.04         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.04         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.83/1.04              (u1_struct_0 @ sk_A))))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['104', '109'])).
% 0.83/1.04  thf('111', plain,
% 0.83/1.04      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.04         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.04         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['61', '110'])).
% 0.83/1.04  thf('112', plain,
% 0.83/1.04      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.83/1.04         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.83/1.04         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['111'])).
% 0.83/1.04  thf('113', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.83/1.04          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['54', '55'])).
% 0.83/1.04  thf('114', plain,
% 0.83/1.04      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.83/1.04         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('clc', [status(thm)], ['112', '113'])).
% 0.83/1.04  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.83/1.04  thf('115', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.83/1.04  thf('116', plain,
% 0.83/1.04      (((~ (v1_xboole_0 @ k1_xboole_0) | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['114', '115'])).
% 0.83/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.04  thf('117', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.04  thf('118', plain,
% 0.83/1.04      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.83/1.04         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.83/1.04      inference('demod', [status(thm)], ['116', '117'])).
% 0.83/1.04  thf('119', plain,
% 0.83/1.04      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.83/1.04         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.83/1.04      inference('split', [status(esa)], ['0'])).
% 0.83/1.04  thf('120', plain,
% 0.83/1.04      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.83/1.04       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.83/1.04      inference('sup-', [status(thm)], ['118', '119'])).
% 0.83/1.04  thf('121', plain, ($false),
% 0.83/1.04      inference('sat_resolution*', [status(thm)], ['1', '59', '60', '120'])).
% 0.83/1.04  
% 0.83/1.04  % SZS output end Refutation
% 0.83/1.04  
% 0.83/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
