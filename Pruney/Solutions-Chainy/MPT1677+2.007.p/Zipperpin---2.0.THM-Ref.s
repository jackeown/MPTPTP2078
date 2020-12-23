%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m2R8Ttrb4Y

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 421 expanded)
%              Number of leaves         :   36 ( 130 expanded)
%              Depth                    :   25
%              Number of atoms          : 2305 (13415 expanded)
%              Number of equality atoms :   46 ( 435 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    ! [X31: $i] :
      ( ( X31
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X31 ) ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X31: $i] :
      ( ~ ( r2_hidden @ X31 @ sk_C )
      | ( X31
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X31 ) ) ) ) ),
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
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X31 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_lattice3 @ X28 @ X27 @ X29 )
      | ( r1_lattice3 @ X28 @ X26 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X31: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( sk_E @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

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

thf('42',plain,(
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

thf('43',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X17 @ ( k2_yellow_0 @ X14 @ X15 ) )
      | ~ ( r1_lattice3 @ X14 @ X15 @ X17 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['12','54'])).

thf('56',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X10 @ ( sk_D @ X10 @ X12 @ X11 ) )
      | ( r1_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['56','61'])).

thf('63',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['25'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('68',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_yellow_0 @ sk_A @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('72',plain,(
    ! [X9: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('73',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('75',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X30 ) @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X9: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('78',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('80',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16
       != ( k2_yellow_0 @ X14 @ X15 ) )
      | ( r1_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_yellow_0 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattice3 @ X14 @ X15 @ ( k2_yellow_0 @ X14 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['73','85'])).

thf('87',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('89',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('90',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('91',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k1_tarski @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['25'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
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

thf('99',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r1_lattice3 @ X24 @ ( k1_tarski @ X25 ) @ X23 )
      | ( r1_orders_2 @ X24 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('107',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
               => ! [D: $i] :
                    ( ( ( r2_lattice3 @ A @ D @ B )
                     => ( r2_lattice3 @ A @ D @ C ) )
                    & ( ( r1_lattice3 @ A @ D @ C )
                     => ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) )).

thf('108',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( r1_lattice3 @ X19 @ X22 @ X20 )
      | ( r1_lattice3 @ X19 @ X22 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['87','115'])).

thf('117',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('119',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['66','119'])).

thf('121',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('123',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['121','122'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('124',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('125',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','64','65','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m2R8Ttrb4Y
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 376 iterations in 0.255s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.46/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.71  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.46/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.71  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.71  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.46/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.71  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.71  thf(sk_E_type, type, sk_E: $i > $i).
% 0.46/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.71  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.46/0.71  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.46/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.71  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.71  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.46/0.71  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.46/0.71  thf(t57_waybel_0, conjecture,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.71         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71               ( ( ( ![D:$i]:
% 0.46/0.71                     ( ( ( v1_finset_1 @ D ) & 
% 0.46/0.71                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.46/0.71                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.46/0.71                         ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.46/0.71                   ( ![D:$i]:
% 0.46/0.71                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.46/0.71                            ( ![E:$i]:
% 0.46/0.71                              ( ( ( v1_finset_1 @ E ) & 
% 0.46/0.71                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.46/0.71                                ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.46/0.71                                     ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.46/0.71                   ( ![D:$i]:
% 0.46/0.71                     ( ( ( v1_finset_1 @ D ) & 
% 0.46/0.71                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.46/0.71                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.46/0.71                         ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.46/0.71                 ( ![D:$i]:
% 0.46/0.71                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71                     ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.46/0.71                       ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i]:
% 0.46/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.71            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.71          ( ![B:$i]:
% 0.46/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71              ( ![C:$i]:
% 0.46/0.71                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71                  ( ( ( ![D:$i]:
% 0.46/0.71                        ( ( ( v1_finset_1 @ D ) & 
% 0.46/0.71                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.46/0.71                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.46/0.71                            ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.46/0.71                      ( ![D:$i]:
% 0.46/0.71                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.46/0.71                               ( ![E:$i]:
% 0.46/0.71                                 ( ( ( v1_finset_1 @ E ) & 
% 0.46/0.71                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.46/0.71                                   ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.46/0.71                                        ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.46/0.71                      ( ![D:$i]:
% 0.46/0.71                        ( ( ( v1_finset_1 @ D ) & 
% 0.46/0.71                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.46/0.71                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.46/0.71                            ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.46/0.71                    ( ![D:$i]:
% 0.46/0.71                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71                        ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.46/0.71                          ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t57_waybel_0])).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | ~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.46/0.71       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(d8_lattice3, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_orders_2 @ A ) =>
% 0.46/0.71       ( ![B:$i,C:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.46/0.71             ( ![D:$i]:
% 0.46/0.71               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('3', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.46/0.71          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.46/0.71          | (r1_lattice3 @ X11 @ X12 @ X10)
% 0.46/0.71          | ~ (l1_orders_2 @ X11))),
% 0.46/0.71      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ sk_A)
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      (![X31 : $i]:
% 0.46/0.71         (((X31) = (k2_yellow_0 @ sk_A @ (sk_E @ X31)))
% 0.46/0.71          | ~ (r2_hidden @ X31 @ sk_C)
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t4_subset, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.71       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X6 @ X7)
% 0.46/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.46/0.71          | (m1_subset_1 @ X6 @ X8))),
% 0.46/0.71      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      (![X31 : $i]:
% 0.46/0.71         (~ (r2_hidden @ X31 @ sk_C)
% 0.46/0.71          | ((X31) = (k2_yellow_0 @ sk_A @ (sk_E @ X31))))),
% 0.46/0.71      inference('clc', [status(thm)], ['7', '10'])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.46/0.71            = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['6', '11'])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('14', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.46/0.71          | (m1_subset_1 @ (sk_D @ X10 @ X12 @ X11) @ (u1_struct_0 @ X11))
% 0.46/0.71          | (r1_lattice3 @ X11 @ X12 @ X10)
% 0.46/0.71          | ~ (l1_orders_2 @ X11))),
% 0.46/0.71      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.46/0.71  thf('16', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ sk_A)
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.71  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('18', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('19', plain,
% 0.46/0.71      (![X31 : $i]:
% 0.46/0.71         ((m1_subset_1 @ (sk_E @ X31) @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.71          | ~ (r2_hidden @ X31 @ sk_C)
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.46/0.71          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.46/0.71             (k1_zfmisc_1 @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.46/0.71           (k1_zfmisc_1 @ sk_B))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['13', '20'])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.46/0.71         (k1_zfmisc_1 @ sk_B))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.71  thf(t3_subset, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      (![X3 : $i, X4 : $i]:
% 0.46/0.71         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('26', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('split', [status(esa)], ['25'])).
% 0.46/0.71  thf('27', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t9_yellow_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_orders_2 @ A ) =>
% 0.46/0.71       ( ![B:$i,C:$i]:
% 0.46/0.71         ( ( r1_tarski @ B @ C ) =>
% 0.46/0.71           ( ![D:$i]:
% 0.46/0.71             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.46/0.71                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.71         (~ (r1_tarski @ X26 @ X27)
% 0.46/0.71          | ~ (r1_lattice3 @ X28 @ X27 @ X29)
% 0.46/0.71          | (r1_lattice3 @ X28 @ X26 @ X29)
% 0.46/0.71          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.46/0.71          | ~ (l1_orders_2 @ X28))),
% 0.46/0.71      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ sk_A)
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.46/0.71          | ~ (r1_tarski @ X0 @ X1))),
% 0.46/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.71  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('31', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.46/0.71          | ~ (r1_tarski @ X0 @ X1))),
% 0.46/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.71  thf('32', plain,
% 0.46/0.71      ((![X0 : $i]:
% 0.46/0.71          (~ (r1_tarski @ X0 @ sk_B) | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['26', '31'])).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.46/0.71            sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['24', '32'])).
% 0.46/0.71  thf('34', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('36', plain,
% 0.46/0.71      (![X31 : $i]:
% 0.46/0.71         ((r2_yellow_0 @ sk_A @ (sk_E @ X31))
% 0.46/0.71          | ~ (r2_hidden @ X31 @ sk_C)
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.46/0.71          | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.71  thf('38', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.71  thf('39', plain,
% 0.46/0.71      (((r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.46/0.71            = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['6', '11'])).
% 0.46/0.71  thf(d10_yellow_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_orders_2 @ A ) =>
% 0.46/0.71       ( ![B:$i,C:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71           ( ( r2_yellow_0 @ A @ B ) =>
% 0.46/0.71             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.46/0.71               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.46/0.71                 ( ![D:$i]:
% 0.46/0.71                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.46/0.71                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('42', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.71         (((X16) != (k2_yellow_0 @ X14 @ X15))
% 0.46/0.71          | ~ (r1_lattice3 @ X14 @ X15 @ X17)
% 0.46/0.71          | (r1_orders_2 @ X14 @ X17 @ X16)
% 0.46/0.71          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.46/0.71          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.46/0.71          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.46/0.71          | ~ (l1_orders_2 @ X14))),
% 0.46/0.71      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ X14)
% 0.46/0.71          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.46/0.71          | ~ (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14))
% 0.46/0.71          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.46/0.71          | (r1_orders_2 @ X14 @ X17 @ (k2_yellow_0 @ X14 @ X15))
% 0.46/0.71          | ~ (r1_lattice3 @ X14 @ X15 @ X17))),
% 0.46/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.46/0.71          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.46/0.71          | ~ (l1_orders_2 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['41', '43'])).
% 0.46/0.71  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('46', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.46/0.71          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 0.46/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.71  thf('47', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.46/0.71          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['40', '46'])).
% 0.46/0.71  thf('48', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.46/0.71          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['39', '48'])).
% 0.46/0.71  thf('50', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.46/0.71          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.46/0.71      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.71  thf('51', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['33', '50'])).
% 0.46/0.71  thf('52', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('53', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.71  thf('54', plain,
% 0.46/0.71      ((((r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71          (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.71  thf('55', plain,
% 0.46/0.71      ((((r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['12', '54'])).
% 0.46/0.71  thf('56', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.71  thf('57', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('58', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.46/0.71          | ~ (r1_orders_2 @ X11 @ X10 @ (sk_D @ X10 @ X12 @ X11))
% 0.46/0.71          | (r1_lattice3 @ X11 @ X12 @ X10)
% 0.46/0.71          | ~ (l1_orders_2 @ X11))),
% 0.46/0.71      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.46/0.71  thf('59', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ sk_A)
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.71  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('61', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.71  thf('62', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('clc', [status(thm)], ['56', '61'])).
% 0.46/0.71  thf('63', plain,
% 0.46/0.71      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.46/0.71         <= (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('64', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.46/0.71       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.71  thf('65', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.46/0.71       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('split', [status(esa)], ['25'])).
% 0.46/0.71  thf('66', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('67', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.71  thf(t63_subset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.71       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (![X1 : $i, X2 : $i]:
% 0.46/0.71         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.46/0.71          | ~ (r2_hidden @ X1 @ X2))),
% 0.46/0.71      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.71  thf('69', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.46/0.71             (k1_zfmisc_1 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.71  thf('70', plain,
% 0.46/0.71      (![X32 : $i]:
% 0.46/0.71         (((X32) = (k1_xboole_0))
% 0.46/0.71          | (r2_yellow_0 @ sk_A @ X32)
% 0.46/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.71          | ~ (v1_finset_1 @ X32))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('71', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.46/0.71        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.71  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.46/0.71  thf('72', plain, (![X9 : $i]: (v1_finset_1 @ (k1_tarski @ X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.46/0.71  thf('73', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.71  thf('74', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.46/0.71             (k1_zfmisc_1 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.71  thf('75', plain,
% 0.46/0.71      (![X30 : $i]:
% 0.46/0.71         (((X30) = (k1_xboole_0))
% 0.46/0.71          | (r2_hidden @ (k2_yellow_0 @ sk_A @ X30) @ sk_C)
% 0.46/0.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.71          | ~ (v1_finset_1 @ X30))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('76', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.46/0.71        | (r2_hidden @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71           sk_C)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.71  thf('77', plain, (![X9 : $i]: (v1_finset_1 @ (k1_tarski @ X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.46/0.71  thf('78', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (r2_hidden @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71           sk_C)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.71  thf('79', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('80', plain,
% 0.46/0.71      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (m1_subset_1 @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71           (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.71  thf('81', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.71         (((X16) != (k2_yellow_0 @ X14 @ X15))
% 0.46/0.71          | (r1_lattice3 @ X14 @ X15 @ X16)
% 0.46/0.71          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.46/0.71          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.46/0.71          | ~ (l1_orders_2 @ X14))),
% 0.46/0.71      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.46/0.71  thf('82', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ X14)
% 0.46/0.71          | ~ (r2_yellow_0 @ X14 @ X15)
% 0.46/0.71          | ~ (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14))
% 0.46/0.71          | (r1_lattice3 @ X14 @ X15 @ (k2_yellow_0 @ X14 @ X15)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['81'])).
% 0.46/0.71  thf('83', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.46/0.71        | ~ (l1_orders_2 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['80', '82'])).
% 0.46/0.71  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))),
% 0.46/0.71      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.71  thf('86', plain,
% 0.46/0.71      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['73', '85'])).
% 0.46/0.71  thf('87', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.46/0.71         (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['86'])).
% 0.46/0.71  thf('88', plain,
% 0.46/0.71      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (m1_subset_1 @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71           (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (r2_hidden @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71           sk_C)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.71  thf('90', plain,
% 0.46/0.71      (![X1 : $i, X2 : $i]:
% 0.46/0.71         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.46/0.71          | ~ (r2_hidden @ X1 @ X2))),
% 0.46/0.71      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.71  thf('91', plain,
% 0.46/0.71      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (m1_subset_1 @ 
% 0.46/0.71           (k1_tarski @ 
% 0.46/0.71            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.46/0.71           (k1_zfmisc_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.71  thf('92', plain,
% 0.46/0.71      (![X3 : $i, X4 : $i]:
% 0.46/0.71         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.71  thf('93', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_tarski @ 
% 0.46/0.71           (k1_tarski @ 
% 0.46/0.71            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.46/0.71           sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.71  thf('94', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('split', [status(esa)], ['25'])).
% 0.46/0.71  thf('95', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.46/0.71          | ~ (r1_tarski @ X0 @ X1))),
% 0.46/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.71  thf('96', plain,
% 0.46/0.71      ((![X0 : $i]:
% 0.46/0.71          (~ (r1_tarski @ X0 @ sk_C) | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.71  thf('97', plain,
% 0.46/0.71      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ 
% 0.46/0.71            (k1_tarski @ 
% 0.46/0.71             (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))) @ 
% 0.46/0.71            sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['93', '96'])).
% 0.46/0.71  thf('98', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t7_yellow_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_orders_2 @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.46/0.71                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.46/0.71                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.46/0.71                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.46/0.71                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.46/0.71                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.46/0.71                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.46/0.71                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('99', plain,
% 0.46/0.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.46/0.71          | ~ (r1_lattice3 @ X24 @ (k1_tarski @ X25) @ X23)
% 0.46/0.71          | (r1_orders_2 @ X24 @ X23 @ X25)
% 0.46/0.71          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.46/0.71          | ~ (l1_orders_2 @ X24))),
% 0.46/0.71      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.46/0.71  thf('100', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (l1_orders_2 @ sk_A)
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.71  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('102', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.46/0.71      inference('demod', [status(thm)], ['100', '101'])).
% 0.46/0.71  thf('103', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71         | ~ (m1_subset_1 @ 
% 0.46/0.71              (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71              (u1_struct_0 @ sk_A))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['97', '102'])).
% 0.46/0.71  thf('104', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['88', '103'])).
% 0.46/0.71  thf('105', plain,
% 0.46/0.71      ((((r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71          (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['104'])).
% 0.46/0.71  thf('106', plain,
% 0.46/0.71      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71        | (m1_subset_1 @ 
% 0.46/0.71           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.46/0.71           (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.71  thf('107', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t4_yellow_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.71               ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.46/0.71                 ( ![D:$i]:
% 0.46/0.71                   ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.46/0.71                       ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.46/0.71                     ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.46/0.71                       ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('108', plain,
% 0.46/0.71      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.46/0.71          | ~ (r1_orders_2 @ X19 @ X18 @ X20)
% 0.46/0.71          | ~ (r1_lattice3 @ X19 @ X22 @ X20)
% 0.46/0.71          | (r1_lattice3 @ X19 @ X22 @ X18)
% 0.46/0.71          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.46/0.71          | ~ (l1_orders_2 @ X19)
% 0.46/0.71          | ~ (v4_orders_2 @ X19))),
% 0.46/0.71      inference('cnf', [status(esa)], [t4_yellow_0])).
% 0.46/0.71  thf('109', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (v4_orders_2 @ sk_A)
% 0.46/0.71          | ~ (l1_orders_2 @ sk_A)
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ X1 @ X0)
% 0.46/0.71          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.71  thf('110', plain, ((v4_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('111', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('112', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ X1 @ X0)
% 0.46/0.71          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.46/0.71  thf('113', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71          | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.46/0.71               (k2_yellow_0 @ sk_A @ 
% 0.46/0.71                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.46/0.71               (k2_yellow_0 @ sk_A @ 
% 0.46/0.71                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['106', '112'])).
% 0.46/0.71  thf('114', plain,
% 0.46/0.71      ((![X0 : $i]:
% 0.46/0.71          ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71           | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.46/0.71                (k2_yellow_0 @ sk_A @ 
% 0.46/0.71                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71           | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['105', '113'])).
% 0.46/0.71  thf('115', plain,
% 0.46/0.71      ((![X0 : $i]:
% 0.46/0.71          (~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.46/0.71              (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.46/0.71           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71           | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['114'])).
% 0.46/0.71  thf('116', plain,
% 0.46/0.71      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.46/0.71            sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['87', '115'])).
% 0.46/0.71  thf('117', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.46/0.71          sk_D_2)
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['116'])).
% 0.46/0.71  thf('118', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.46/0.71          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.46/0.71      inference('demod', [status(thm)], ['100', '101'])).
% 0.46/0.71  thf('119', plain,
% 0.46/0.71      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.46/0.71         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.46/0.71              (u1_struct_0 @ sk_A))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.71  thf('120', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['66', '119'])).
% 0.46/0.71  thf('121', plain,
% 0.46/0.71      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.46/0.71         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.46/0.71         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['120'])).
% 0.46/0.71  thf('122', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.46/0.71          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.71  thf('123', plain,
% 0.46/0.71      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.46/0.71         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('clc', [status(thm)], ['121', '122'])).
% 0.46/0.71  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.46/0.71  thf('124', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.46/0.71  thf('125', plain,
% 0.46/0.71      (((~ (v1_xboole_0 @ k1_xboole_0) | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['123', '124'])).
% 0.46/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.71  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.71  thf('127', plain,
% 0.46/0.71      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.46/0.71         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.46/0.71      inference('demod', [status(thm)], ['125', '126'])).
% 0.46/0.71  thf('128', plain,
% 0.46/0.71      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.46/0.71         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.46/0.71      inference('split', [status(esa)], ['0'])).
% 0.46/0.71  thf('129', plain,
% 0.46/0.71      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.46/0.71       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.46/0.71      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.71  thf('130', plain, ($false),
% 0.46/0.71      inference('sat_resolution*', [status(thm)], ['1', '64', '65', '129'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.58/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
