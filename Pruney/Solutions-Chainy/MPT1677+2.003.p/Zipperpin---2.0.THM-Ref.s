%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d3zkuyaHNh

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:47 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 765 expanded)
%              Number of leaves         :   36 ( 221 expanded)
%              Depth                    :   29
%              Number of atoms          : 1892 (24446 expanded)
%              Number of equality atoms :   30 ( 790 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_yellow_0 @ sk_A @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('18',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
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

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X13
       != ( k2_yellow_0 @ X11 @ X12 ) )
      | ( r1_lattice3 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( r2_yellow_0 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_lattice3 @ X11 @ X12 @ ( k2_yellow_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X29 ) @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('31',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_orders_2 @ X8 @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ sk_C ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X17 @ X19 )
      | ~ ( r1_lattice3 @ X18 @ X21 @ X19 )
      | ( r1_lattice3 @ X18 @ X21 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['26','55'])).

thf('57',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_lattice3 @ X23 @ ( k1_tarski @ X24 ) @ X22 )
      | ( r1_orders_2 @ X23 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','63'])).

thf('65',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ ( sk_D @ X7 @ X9 @ X8 ) )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['65','70'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('73',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','77'])).

thf('79',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('82',plain,(
    ! [X30: $i] :
      ( ( X30
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X30 ) ) )
      | ~ ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('88',plain,(
    ! [X30: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( sk_E @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('94',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X30 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['96'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('98',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['32'])).

thf('101',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['32'])).

thf('102',plain,(
    r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['2','77','101'])).

thf('103',plain,(
    r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['100','102'])).

thf('104',plain,(
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

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_lattice3 @ X27 @ X26 @ X28 )
      | ( r1_lattice3 @ X27 @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('112',plain,(
    r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('115',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_yellow_0 @ X11 @ X12 ) )
      | ~ ( r1_lattice3 @ X11 @ X12 @ X14 )
      | ( r1_orders_2 @ X11 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('116',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( r2_yellow_0 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X14 @ ( k2_yellow_0 @ X11 @ X12 ) )
      | ~ ( r1_lattice3 @ X11 @ X12 @ X14 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['112','121'])).

thf('123',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','122'])).

thf('124',plain,(
    ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('125',plain,(
    r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['85','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('128',plain,(
    r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['79','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d3zkuyaHNh
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 308 iterations in 0.261s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(sk_E_type, type, sk_E: $i > $i).
% 0.51/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.51/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.51/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.72  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.51/0.72  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.51/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.72  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.51/0.72  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.51/0.72  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.51/0.72  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.51/0.72  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.51/0.72  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.51/0.72  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.51/0.72  thf(t57_waybel_0, conjecture,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.51/0.72         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72           ( ![C:$i]:
% 0.51/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72               ( ( ( ![D:$i]:
% 0.51/0.72                     ( ( ( v1_finset_1 @ D ) & 
% 0.51/0.72                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.51/0.72                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.51/0.72                         ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.51/0.72                   ( ![D:$i]:
% 0.51/0.72                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.51/0.72                            ( ![E:$i]:
% 0.51/0.72                              ( ( ( v1_finset_1 @ E ) & 
% 0.51/0.72                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.51/0.72                                ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.51/0.72                                     ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.51/0.72                   ( ![D:$i]:
% 0.51/0.72                     ( ( ( v1_finset_1 @ D ) & 
% 0.51/0.72                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.51/0.72                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.51/0.72                         ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.51/0.72                 ( ![D:$i]:
% 0.51/0.72                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72                     ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.51/0.72                       ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i]:
% 0.51/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.51/0.72            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.72          ( ![B:$i]:
% 0.51/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72              ( ![C:$i]:
% 0.51/0.72                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.72                  ( ( ( ![D:$i]:
% 0.51/0.72                        ( ( ( v1_finset_1 @ D ) & 
% 0.51/0.72                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.51/0.72                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.51/0.72                            ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.51/0.72                      ( ![D:$i]:
% 0.51/0.72                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.51/0.72                               ( ![E:$i]:
% 0.51/0.72                                 ( ( ( v1_finset_1 @ E ) & 
% 0.51/0.72                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.51/0.72                                   ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.51/0.72                                        ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.51/0.72                      ( ![D:$i]:
% 0.51/0.72                        ( ( ( v1_finset_1 @ D ) & 
% 0.51/0.72                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.51/0.72                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.51/0.72                            ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.51/0.72                    ( ![D:$i]:
% 0.51/0.72                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72                        ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.51/0.72                          ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t57_waybel_0])).
% 0.51/0.72  thf('0', plain,
% 0.51/0.72      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | ~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.51/0.72         <= (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('split', [status(esa)], ['0'])).
% 0.51/0.72  thf('2', plain,
% 0.51/0.72      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.51/0.72       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.51/0.72      inference('split', [status(esa)], ['0'])).
% 0.51/0.72  thf('3', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(d8_lattice3, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_orders_2 @ A ) =>
% 0.51/0.72       ( ![B:$i,C:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.51/0.72             ( ![D:$i]:
% 0.51/0.72               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('4', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.51/0.72          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ (u1_struct_0 @ X8))
% 0.51/0.72          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.51/0.72          | ~ (l1_orders_2 @ X8))),
% 0.51/0.72      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.72  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('7', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.51/0.72  thf('8', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.51/0.72          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.51/0.72          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.51/0.72          | ~ (l1_orders_2 @ X8))),
% 0.51/0.72      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.51/0.72  thf('10', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.72  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['10', '11'])).
% 0.51/0.72  thf(t63_subset_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( r2_hidden @ A @ B ) =>
% 0.51/0.72       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.51/0.72  thf('13', plain,
% 0.51/0.72      (![X1 : $i, X2 : $i]:
% 0.51/0.72         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.51/0.72          | ~ (r2_hidden @ X1 @ X2))),
% 0.51/0.72      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.51/0.72             (k1_zfmisc_1 @ X0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.72  thf('15', plain,
% 0.51/0.72      (![X31 : $i]:
% 0.51/0.72         (((X31) = (k1_xboole_0))
% 0.51/0.72          | (r2_yellow_0 @ sk_A @ X31)
% 0.51/0.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ sk_B))
% 0.51/0.72          | ~ (v1_finset_1 @ X31))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('16', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.51/0.72        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.51/0.72        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.72  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.51/0.72  thf('17', plain, (![X6 : $i]: (v1_finset_1 @ (k1_tarski @ X6))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.51/0.72        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.51/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.51/0.72  thf(dt_k2_yellow_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( l1_orders_2 @ A ) =>
% 0.51/0.72       ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X15)
% 0.51/0.72          | (m1_subset_1 @ (k2_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.51/0.72  thf(d10_yellow_0, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_orders_2 @ A ) =>
% 0.51/0.72       ( ![B:$i,C:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72           ( ( r2_yellow_0 @ A @ B ) =>
% 0.51/0.72             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.51/0.72               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.51/0.72                 ( ![D:$i]:
% 0.51/0.72                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.51/0.72                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.72         (((X13) != (k2_yellow_0 @ X11 @ X12))
% 0.51/0.72          | (r1_lattice3 @ X11 @ X12 @ X13)
% 0.51/0.72          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.51/0.72          | ~ (r2_yellow_0 @ X11 @ X12)
% 0.51/0.72          | ~ (l1_orders_2 @ X11))),
% 0.51/0.72      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.51/0.72  thf('21', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X11)
% 0.51/0.72          | ~ (r2_yellow_0 @ X11 @ X12)
% 0.51/0.72          | ~ (m1_subset_1 @ (k2_yellow_0 @ X11 @ X12) @ (u1_struct_0 @ X11))
% 0.51/0.72          | (r1_lattice3 @ X11 @ X12 @ (k2_yellow_0 @ X11 @ X12)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['20'])).
% 0.51/0.72  thf('22', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X0)
% 0.51/0.72          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.51/0.72          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.51/0.72          | ~ (l1_orders_2 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['19', '21'])).
% 0.51/0.72  thf('23', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (r2_yellow_0 @ X0 @ X1)
% 0.51/0.72          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.51/0.72          | ~ (l1_orders_2 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['22'])).
% 0.51/0.72  thf('24', plain,
% 0.51/0.72      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72        | ~ (l1_orders_2 @ sk_A)
% 0.51/0.72        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.51/0.72           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['18', '23'])).
% 0.51/0.72  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.51/0.72           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.51/0.72      inference('demod', [status(thm)], ['24', '25'])).
% 0.51/0.72  thf('27', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.51/0.72             (k1_zfmisc_1 @ X0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.72  thf('28', plain,
% 0.51/0.72      (![X29 : $i]:
% 0.51/0.72         (((X29) = (k1_xboole_0))
% 0.51/0.72          | (r2_hidden @ (k2_yellow_0 @ sk_A @ X29) @ sk_C)
% 0.51/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ sk_B))
% 0.51/0.72          | ~ (v1_finset_1 @ X29))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('29', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.51/0.72        | (r2_hidden @ 
% 0.51/0.72           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.51/0.72           sk_C)
% 0.51/0.72        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.72  thf('30', plain, (![X6 : $i]: (v1_finset_1 @ (k1_tarski @ X6))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.51/0.72  thf('31', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72        | (r2_hidden @ 
% 0.51/0.72           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.51/0.72           sk_C)
% 0.51/0.72        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.51/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.72  thf('32', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('33', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('split', [status(esa)], ['32'])).
% 0.51/0.72  thf('34', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X15)
% 0.51/0.72          | (m1_subset_1 @ (k2_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.51/0.72  thf('35', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('36', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.51/0.72          | ~ (r1_lattice3 @ X8 @ X9 @ X7)
% 0.51/0.72          | ~ (r2_hidden @ X10 @ X9)
% 0.51/0.72          | (r1_orders_2 @ X8 @ X7 @ X10)
% 0.51/0.72          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.51/0.72          | ~ (l1_orders_2 @ X8))),
% 0.51/0.72      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.51/0.72  thf('37', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.51/0.72          | ~ (r2_hidden @ X0 @ X1)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.51/0.72  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('39', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.51/0.72          | ~ (r2_hidden @ X0 @ X1)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.51/0.72      inference('demod', [status(thm)], ['37', '38'])).
% 0.51/0.72  thf('40', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.51/0.72          | ~ (r2_hidden @ (k2_yellow_0 @ sk_A @ X0) @ X1)
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['34', '39'])).
% 0.51/0.72  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('42', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.51/0.72          | ~ (r2_hidden @ (k2_yellow_0 @ sk_A @ X0) @ X1)
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.51/0.72      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.72  thf('43', plain,
% 0.51/0.72      ((![X0 : $i]:
% 0.51/0.72          ((r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72           | ~ (r2_hidden @ (k2_yellow_0 @ sk_A @ X0) @ sk_C)))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['33', '42'])).
% 0.51/0.72  thf('44', plain,
% 0.51/0.72      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.51/0.72            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['31', '43'])).
% 0.51/0.72  thf('45', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X15)
% 0.51/0.72          | (m1_subset_1 @ (k2_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.51/0.72  thf('46', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t4_yellow_0, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72           ( ![C:$i]:
% 0.51/0.72             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72               ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.51/0.72                 ( ![D:$i]:
% 0.51/0.72                   ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.51/0.72                       ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.51/0.72                     ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.51/0.72                       ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('47', plain,
% 0.51/0.72      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.51/0.72          | ~ (r1_orders_2 @ X18 @ X17 @ X19)
% 0.51/0.72          | ~ (r1_lattice3 @ X18 @ X21 @ X19)
% 0.51/0.72          | (r1_lattice3 @ X18 @ X21 @ X17)
% 0.51/0.72          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.51/0.72          | ~ (l1_orders_2 @ X18)
% 0.51/0.72          | ~ (v4_orders_2 @ X18))),
% 0.51/0.72      inference('cnf', [status(esa)], [t4_yellow_0])).
% 0.51/0.72  thf('48', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (v4_orders_2 @ sk_A)
% 0.51/0.72          | ~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ X0)
% 0.51/0.72          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.72  thf('49', plain, ((v4_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('51', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ X0)
% 0.51/0.72          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.51/0.72  thf('52', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['45', '51'])).
% 0.51/0.72  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('54', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.51/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.51/0.72  thf('55', plain,
% 0.51/0.72      ((![X0 : $i]:
% 0.51/0.72          ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72           | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.51/0.72                (k2_yellow_0 @ sk_A @ 
% 0.51/0.72                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['44', '54'])).
% 0.51/0.72  thf('56', plain,
% 0.51/0.72      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.51/0.72            sk_D_2)
% 0.51/0.72         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['26', '55'])).
% 0.51/0.72  thf('57', plain,
% 0.51/0.72      ((((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.51/0.72          sk_D_2)
% 0.51/0.72         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['56'])).
% 0.51/0.72  thf('58', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t7_yellow_0, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_orders_2 @ A ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72           ( ![C:$i]:
% 0.51/0.72             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.51/0.72                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.51/0.72                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.51/0.72                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.51/0.72                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.51/0.72                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.51/0.72                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.51/0.72                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('59', plain,
% 0.51/0.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.51/0.72          | ~ (r1_lattice3 @ X23 @ (k1_tarski @ X24) @ X22)
% 0.51/0.72          | (r1_orders_2 @ X23 @ X22 @ X24)
% 0.51/0.72          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.51/0.72          | ~ (l1_orders_2 @ X23))),
% 0.51/0.72      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.51/0.72  thf('60', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['58', '59'])).
% 0.51/0.72  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('62', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.51/0.72      inference('demod', [status(thm)], ['60', '61'])).
% 0.51/0.72  thf('63', plain,
% 0.51/0.72      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.51/0.72         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.51/0.72              (u1_struct_0 @ sk_A))))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['57', '62'])).
% 0.51/0.72  thf('64', plain,
% 0.51/0.72      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.51/0.72         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['7', '63'])).
% 0.51/0.72  thf('65', plain,
% 0.51/0.72      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.51/0.72         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.51/0.72         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['64'])).
% 0.51/0.72  thf('66', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('67', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.51/0.72          | ~ (r1_orders_2 @ X8 @ X7 @ (sk_D @ X7 @ X9 @ X8))
% 0.51/0.72          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.51/0.72          | ~ (l1_orders_2 @ X8))),
% 0.51/0.72      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.51/0.72  thf('68', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.72  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('70', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['68', '69'])).
% 0.51/0.72  thf('71', plain,
% 0.51/0.72      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.51/0.72         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('clc', [status(thm)], ['65', '70'])).
% 0.51/0.72  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.51/0.72  thf('72', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.51/0.72  thf('73', plain,
% 0.51/0.72      (((~ (v1_xboole_0 @ k1_xboole_0) | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['71', '72'])).
% 0.51/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.72  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.72  thf('75', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.51/0.72      inference('demod', [status(thm)], ['73', '74'])).
% 0.51/0.72  thf('76', plain,
% 0.51/0.72      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.51/0.72         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.51/0.72      inference('split', [status(esa)], ['0'])).
% 0.51/0.72  thf('77', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.51/0.72       ~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['75', '76'])).
% 0.51/0.72  thf('78', plain, (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)], ['2', '77'])).
% 0.51/0.72  thf('79', plain, (~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.51/0.72  thf('80', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['10', '11'])).
% 0.51/0.72  thf('81', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.51/0.72  thf('82', plain,
% 0.51/0.72      (![X30 : $i]:
% 0.51/0.72         (((X30) = (k2_yellow_0 @ sk_A @ (sk_E @ X30)))
% 0.51/0.72          | ~ (r2_hidden @ X30 @ sk_C)
% 0.51/0.72          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('83', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.51/0.72          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.51/0.72              = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['81', '82'])).
% 0.51/0.72  thf('84', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.51/0.72            = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['80', '83'])).
% 0.51/0.72  thf('85', plain,
% 0.51/0.72      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.51/0.72          = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('simplify', [status(thm)], ['84'])).
% 0.51/0.72  thf('86', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['10', '11'])).
% 0.51/0.72  thf('87', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.51/0.72  thf('88', plain,
% 0.51/0.72      (![X30 : $i]:
% 0.51/0.72         ((r2_yellow_0 @ sk_A @ (sk_E @ X30))
% 0.51/0.72          | ~ (r2_hidden @ X30 @ sk_C)
% 0.51/0.72          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('89', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.51/0.72          | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['87', '88'])).
% 0.51/0.72  thf('90', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['86', '89'])).
% 0.51/0.72  thf('91', plain,
% 0.51/0.72      (((r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('simplify', [status(thm)], ['90'])).
% 0.51/0.72  thf('92', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['10', '11'])).
% 0.51/0.72  thf('93', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.51/0.72  thf('94', plain,
% 0.51/0.72      (![X30 : $i]:
% 0.51/0.72         ((m1_subset_1 @ (sk_E @ X30) @ (k1_zfmisc_1 @ sk_B))
% 0.51/0.72          | ~ (r2_hidden @ X30 @ sk_C)
% 0.51/0.72          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('95', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.51/0.72          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.51/0.72             (k1_zfmisc_1 @ sk_B)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['93', '94'])).
% 0.51/0.72  thf('96', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.51/0.72           (k1_zfmisc_1 @ sk_B))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['92', '95'])).
% 0.51/0.72  thf('97', plain,
% 0.51/0.72      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.51/0.72         (k1_zfmisc_1 @ sk_B))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('simplify', [status(thm)], ['96'])).
% 0.51/0.72  thf(t3_subset, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.72  thf('98', plain,
% 0.51/0.72      (![X3 : $i, X4 : $i]:
% 0.51/0.72         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.72  thf('99', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.51/0.72      inference('sup-', [status(thm)], ['97', '98'])).
% 0.51/0.72  thf('100', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.51/0.72         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.51/0.72      inference('split', [status(esa)], ['32'])).
% 0.51/0.72  thf('101', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.51/0.72       ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('split', [status(esa)], ['32'])).
% 0.51/0.72  thf('102', plain, (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.51/0.72      inference('sat_resolution*', [status(thm)], ['2', '77', '101'])).
% 0.51/0.72  thf('103', plain, ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['100', '102'])).
% 0.51/0.72  thf('104', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t9_yellow_0, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( l1_orders_2 @ A ) =>
% 0.51/0.72       ( ![B:$i,C:$i]:
% 0.51/0.72         ( ( r1_tarski @ B @ C ) =>
% 0.51/0.72           ( ![D:$i]:
% 0.51/0.72             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.72               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.51/0.72                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('105', plain,
% 0.51/0.72      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X25 @ X26)
% 0.51/0.72          | ~ (r1_lattice3 @ X27 @ X26 @ X28)
% 0.51/0.72          | (r1_lattice3 @ X27 @ X25 @ X28)
% 0.51/0.72          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.51/0.72          | ~ (l1_orders_2 @ X27))),
% 0.51/0.72      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.51/0.72  thf('106', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.51/0.72          | ~ (r1_tarski @ X0 @ X1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['104', '105'])).
% 0.51/0.72  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('108', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.51/0.72          | ~ (r1_tarski @ X0 @ X1))),
% 0.51/0.72      inference('demod', [status(thm)], ['106', '107'])).
% 0.51/0.72  thf('109', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X0 @ sk_B) | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['103', '108'])).
% 0.51/0.72  thf('110', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['99', '109'])).
% 0.51/0.72  thf('111', plain, (~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.51/0.72  thf('112', plain,
% 0.51/0.72      ((r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2)),
% 0.51/0.72      inference('clc', [status(thm)], ['110', '111'])).
% 0.51/0.72  thf('113', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('114', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X15)
% 0.51/0.72          | (m1_subset_1 @ (k2_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.51/0.72  thf('115', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.72         (((X13) != (k2_yellow_0 @ X11 @ X12))
% 0.51/0.72          | ~ (r1_lattice3 @ X11 @ X12 @ X14)
% 0.51/0.72          | (r1_orders_2 @ X11 @ X14 @ X13)
% 0.51/0.72          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.51/0.72          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.51/0.72          | ~ (r2_yellow_0 @ X11 @ X12)
% 0.51/0.72          | ~ (l1_orders_2 @ X11))),
% 0.51/0.72      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.51/0.72  thf('116', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X11)
% 0.51/0.72          | ~ (r2_yellow_0 @ X11 @ X12)
% 0.51/0.72          | ~ (m1_subset_1 @ (k2_yellow_0 @ X11 @ X12) @ (u1_struct_0 @ X11))
% 0.51/0.72          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.51/0.72          | (r1_orders_2 @ X11 @ X14 @ (k2_yellow_0 @ X11 @ X12))
% 0.51/0.72          | ~ (r1_lattice3 @ X11 @ X12 @ X14))),
% 0.51/0.72      inference('simplify', [status(thm)], ['115'])).
% 0.51/0.72  thf('117', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ X0)
% 0.51/0.72          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.51/0.72          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.51/0.72          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.51/0.72          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.51/0.72          | ~ (l1_orders_2 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['114', '116'])).
% 0.51/0.72  thf('118', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (r2_yellow_0 @ X0 @ X1)
% 0.51/0.72          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.51/0.72          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.51/0.72          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.51/0.72          | ~ (l1_orders_2 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['117'])).
% 0.51/0.72  thf('119', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (l1_orders_2 @ sk_A)
% 0.51/0.72          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72          | ~ (r2_yellow_0 @ sk_A @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['113', '118'])).
% 0.51/0.72  thf('120', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('121', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | (r1_orders_2 @ sk_A @ sk_D_2 @ (k2_yellow_0 @ sk_A @ X0))
% 0.51/0.72          | ~ (r2_yellow_0 @ sk_A @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['119', '120'])).
% 0.51/0.72  thf('122', plain,
% 0.51/0.72      ((~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.51/0.72        | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.51/0.72           (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['112', '121'])).
% 0.51/0.72  thf('123', plain,
% 0.51/0.72      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.51/0.72        | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.51/0.72           (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['91', '122'])).
% 0.51/0.72  thf('124', plain, (~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.51/0.72      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.51/0.72  thf('125', plain,
% 0.51/0.72      ((r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.51/0.72        (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 0.51/0.72      inference('clc', [status(thm)], ['123', '124'])).
% 0.51/0.72  thf('126', plain,
% 0.51/0.72      (((r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))
% 0.51/0.72        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.51/0.72      inference('sup+', [status(thm)], ['85', '125'])).
% 0.51/0.72  thf('127', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.51/0.72          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['68', '69'])).
% 0.51/0.72  thf('128', plain, ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.51/0.72      inference('clc', [status(thm)], ['126', '127'])).
% 0.51/0.72  thf('129', plain, ($false), inference('demod', [status(thm)], ['79', '128'])).
% 0.51/0.72  
% 0.51/0.72  % SZS output end Refutation
% 0.51/0.72  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
