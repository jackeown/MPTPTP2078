%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qXg75pChK7

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:45 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 773 expanded)
%              Number of leaves         :   36 ( 225 expanded)
%              Depth                    :   31
%              Number of atoms          : 1923 (24074 expanded)
%              Number of equality atoms :   31 ( 770 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

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
   <= ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('20',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

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

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14
       != ( k1_yellow_0 @ X12 @ X13 ) )
      | ( r2_lattice3 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r2_lattice3 @ X12 @ X13 @ ( k1_yellow_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X30 ) @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('33',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_orders_2 @ X9 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

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

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( r2_lattice3 @ X19 @ X21 @ X18 )
      | ( r2_lattice3 @ X19 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X3 @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['28','55'])).

thf('57',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_lattice3 @ X24 @ ( k1_tarski @ X25 ) @ X23 )
      | ( r1_orders_2 @ X24 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','63'])).

thf('65',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_orders_2 @ X9 @ ( sk_D @ X8 @ X10 @ X9 ) @ X8 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
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
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','77'])).

thf('79',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('82',plain,(
    ! [X31: $i] :
      ( ( X31
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X31 ) ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('88',plain,(
    ! [X31: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('94',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X31 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['34'])).

thf('101',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['34'])).

thf('102',plain,(
    r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['2','77','101'])).

thf('103',plain,(
    r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r2_lattice3 @ X28 @ X27 @ X29 )
      | ( r2_lattice3 @ X28 @ X26 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('112',plain,(
    r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('115',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k1_yellow_0 @ X12 @ X13 ) )
      | ~ ( r2_lattice3 @ X12 @ X13 @ X15 )
      | ( r1_orders_2 @ X12 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('116',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ ( k1_yellow_0 @ X12 @ X13 ) @ X15 )
      | ~ ( r2_lattice3 @ X12 @ X13 @ X15 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['112','121'])).

thf('123',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['91','122'])).

thf('124',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('125',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['85','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('128',plain,(
    r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['79','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qXg75pChK7
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 310 iterations in 0.345s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.58/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.58/0.80  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.58/0.80  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.58/0.80  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.58/0.80  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.58/0.80  thf(sk_E_type, type, sk_E: $i > $i).
% 0.58/0.80  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.58/0.80  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.58/0.80  thf(t52_waybel_0, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.80         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80               ( ( ( ![D:$i]:
% 0.58/0.80                     ( ( ( v1_finset_1 @ D ) & 
% 0.58/0.80                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.58/0.80                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.58/0.80                         ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 0.58/0.80                   ( ![D:$i]:
% 0.58/0.80                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.58/0.80                            ( ![E:$i]:
% 0.58/0.80                              ( ( ( v1_finset_1 @ E ) & 
% 0.58/0.80                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.58/0.80                                ( ~( ( r1_yellow_0 @ A @ E ) & 
% 0.58/0.80                                     ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.58/0.80                   ( ![D:$i]:
% 0.58/0.80                     ( ( ( v1_finset_1 @ D ) & 
% 0.58/0.80                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.58/0.80                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.58/0.80                         ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.58/0.80                 ( ![D:$i]:
% 0.58/0.80                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                     ( ( r2_lattice3 @ A @ B @ D ) <=>
% 0.58/0.80                       ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.80            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80              ( ![C:$i]:
% 0.58/0.80                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80                  ( ( ( ![D:$i]:
% 0.58/0.80                        ( ( ( v1_finset_1 @ D ) & 
% 0.58/0.80                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.58/0.80                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.58/0.80                            ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 0.58/0.80                      ( ![D:$i]:
% 0.58/0.80                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.58/0.80                               ( ![E:$i]:
% 0.58/0.80                                 ( ( ( v1_finset_1 @ E ) & 
% 0.58/0.80                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.58/0.80                                   ( ~( ( r1_yellow_0 @ A @ E ) & 
% 0.58/0.80                                        ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.58/0.80                      ( ![D:$i]:
% 0.58/0.80                        ( ( ( v1_finset_1 @ D ) & 
% 0.58/0.80                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.58/0.80                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.58/0.80                            ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.58/0.80                    ( ![D:$i]:
% 0.58/0.80                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                        ( ( r2_lattice3 @ A @ B @ D ) <=>
% 0.58/0.80                          ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t52_waybel_0])).
% 0.58/0.80  thf('0', plain,
% 0.58/0.80      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.58/0.80         <= (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.58/0.80       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('3', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(d9_lattice3, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_orders_2 @ A ) =>
% 0.58/0.80       ( ![B:$i,C:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.58/0.80             ( ![D:$i]:
% 0.58/0.80               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.58/0.80          | (m1_subset_1 @ (sk_D @ X8 @ X10 @ X9) @ (u1_struct_0 @ X9))
% 0.58/0.80          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.58/0.80          | ~ (l1_orders_2 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.80  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.80  thf('8', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.58/0.80          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.58/0.80          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.58/0.80          | ~ (l1_orders_2 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.80  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.80  thf(l1_zfmisc_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X1 : $i, X3 : $i]:
% 0.58/0.80         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r1_tarski @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.80  thf(t3_subset, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X4 : $i, X6 : $i]:
% 0.58/0.80         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.58/0.80             (k1_zfmisc_1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X32 : $i]:
% 0.58/0.80         (((X32) = (k1_xboole_0))
% 0.58/0.80          | (r1_yellow_0 @ sk_A @ X32)
% 0.58/0.80          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ sk_B))
% 0.58/0.80          | ~ (v1_finset_1 @ X32))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.58/0.80        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.58/0.80        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.58/0.80  thf('19', plain, (![X7 : $i]: (v1_finset_1 @ (k1_tarski @ X7))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.58/0.80        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf(dt_k1_yellow_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( l1_orders_2 @ A ) =>
% 0.58/0.80       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X16)
% 0.58/0.80          | (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.58/0.80  thf(d9_yellow_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_orders_2 @ A ) =>
% 0.58/0.80       ( ![B:$i,C:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ( r1_yellow_0 @ A @ B ) =>
% 0.58/0.80             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.58/0.80               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.58/0.80                 ( ![D:$i]:
% 0.58/0.80                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.58/0.80                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.80         (((X14) != (k1_yellow_0 @ X12 @ X13))
% 0.58/0.80          | (r2_lattice3 @ X12 @ X13 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.58/0.80          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.58/0.80          | ~ (l1_orders_2 @ X12))),
% 0.58/0.80      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X12)
% 0.58/0.80          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.58/0.80          | ~ (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12))
% 0.58/0.80          | (r2_lattice3 @ X12 @ X13 @ (k1_yellow_0 @ X12 @ X13)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X0)
% 0.58/0.80          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.58/0.80          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.58/0.80          | ~ (l1_orders_2 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['21', '23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_yellow_0 @ X0 @ X1)
% 0.58/0.80          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.58/0.80          | ~ (l1_orders_2 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['24'])).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80        | ~ (l1_orders_2 @ sk_A)
% 0.58/0.80        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.58/0.80           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['20', '25'])).
% 0.58/0.80  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.58/0.80           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['26', '27'])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.58/0.80             (k1_zfmisc_1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (![X30 : $i]:
% 0.58/0.80         (((X30) = (k1_xboole_0))
% 0.58/0.80          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X30) @ sk_C)
% 0.58/0.80          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ sk_B))
% 0.58/0.80          | ~ (v1_finset_1 @ X30))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.58/0.80        | (r2_hidden @ 
% 0.58/0.80           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.58/0.80           sk_C)
% 0.58/0.80        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.80  thf('32', plain, (![X7 : $i]: (v1_finset_1 @ (k1_tarski @ X7))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80        | (r2_hidden @ 
% 0.58/0.80           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.58/0.80           sk_C)
% 0.58/0.80        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('split', [status(esa)], ['34'])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X16)
% 0.58/0.80          | (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.58/0.80  thf('37', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('38', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.58/0.80          | ~ (r2_lattice3 @ X9 @ X10 @ X8)
% 0.58/0.80          | ~ (r2_hidden @ X11 @ X10)
% 0.58/0.80          | (r1_orders_2 @ X9 @ X11 @ X8)
% 0.58/0.80          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.58/0.80          | ~ (l1_orders_2 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ X0 @ X1)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.80  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('41', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ X0 @ X1)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['39', '40'])).
% 0.58/0.80  thf('42', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.58/0.80          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['36', '41'])).
% 0.58/0.80  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.58/0.80          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.80  thf('45', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2)
% 0.58/0.80           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_C)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['35', '44'])).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80         | (r1_orders_2 @ sk_A @ 
% 0.58/0.80            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.58/0.80            sk_D_2)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['33', '45'])).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X16)
% 0.58/0.80          | (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.58/0.80  thf(t4_yellow_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80               ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.58/0.80                 ( ![D:$i]:
% 0.58/0.80                   ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.58/0.80                       ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.58/0.80                     ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.58/0.80                       ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('48', plain,
% 0.58/0.80      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.58/0.80          | ~ (r1_orders_2 @ X19 @ X18 @ X20)
% 0.58/0.80          | ~ (r2_lattice3 @ X19 @ X21 @ X18)
% 0.58/0.80          | (r2_lattice3 @ X19 @ X21 @ X20)
% 0.58/0.80          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.58/0.80          | ~ (l1_orders_2 @ X19)
% 0.58/0.80          | ~ (v4_orders_2 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_yellow_0])).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X0)
% 0.58/0.80          | ~ (v4_orders_2 @ X0)
% 0.58/0.80          | ~ (l1_orders_2 @ X0)
% 0.58/0.80          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.58/0.80          | (r2_lattice3 @ X0 @ X3 @ X2)
% 0.58/0.80          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.58/0.80          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.58/0.80          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.58/0.80          | (r2_lattice3 @ X0 @ X3 @ X2)
% 0.58/0.80          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.58/0.80          | ~ (v4_orders_2 @ X0)
% 0.58/0.80          | ~ (l1_orders_2 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['49'])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80           | ~ (l1_orders_2 @ sk_A)
% 0.58/0.80           | ~ (v4_orders_2 @ sk_A)
% 0.58/0.80           | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.58/0.80           | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80           | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.58/0.80                (k1_yellow_0 @ sk_A @ 
% 0.58/0.80                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['46', '50'])).
% 0.58/0.80  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('54', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      ((![X0 : $i]:
% 0.58/0.80          ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80           | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80           | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.58/0.80                (k1_yellow_0 @ sk_A @ 
% 0.58/0.80                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.58/0.80            sk_D_2)
% 0.58/0.80         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['28', '55'])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      ((((r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.58/0.80          sk_D_2)
% 0.58/0.80         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['56'])).
% 0.58/0.80  thf('58', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t7_yellow_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_orders_2 @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.58/0.80                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.58/0.80                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.58/0.80                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.58/0.80                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.58/0.80                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.58/0.80                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.58/0.80                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('59', plain,
% 0.58/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.58/0.80          | ~ (r2_lattice3 @ X24 @ (k1_tarski @ X25) @ X23)
% 0.58/0.80          | (r1_orders_2 @ X24 @ X25 @ X23)
% 0.58/0.80          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.58/0.80          | ~ (l1_orders_2 @ X24))),
% 0.58/0.80      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.58/0.80  thf('63', plain,
% 0.58/0.80      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.58/0.80         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.58/0.80              (u1_struct_0 @ sk_A))))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['57', '62'])).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.58/0.80         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '63'])).
% 0.58/0.80  thf('65', plain,
% 0.58/0.80      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.58/0.80         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.58/0.80         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.80  thf('66', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('67', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.58/0.80          | ~ (r1_orders_2 @ X9 @ (sk_D @ X8 @ X10 @ X9) @ X8)
% 0.58/0.80          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.58/0.80          | ~ (l1_orders_2 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.58/0.80  thf('68', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['66', '67'])).
% 0.58/0.80  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.58/0.80         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('clc', [status(thm)], ['65', '70'])).
% 0.58/0.80  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.58/0.80  thf('72', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (((~ (v1_xboole_0 @ k1_xboole_0) | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['71', '72'])).
% 0.58/0.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.80  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.80  thf('75', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.58/0.80      inference('demod', [status(thm)], ['73', '74'])).
% 0.58/0.80  thf('76', plain,
% 0.58/0.80      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.58/0.80         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.58/0.80       ~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['75', '76'])).
% 0.58/0.80  thf('78', plain, (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['2', '77'])).
% 0.58/0.80  thf('79', plain, (~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.80  thf('81', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      (![X31 : $i]:
% 0.58/0.80         (((X31) = (k1_yellow_0 @ sk_A @ (sk_E @ X31)))
% 0.58/0.80          | ~ (r2_hidden @ X31 @ sk_C)
% 0.58/0.80          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.58/0.80          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.58/0.80              = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.80  thf('84', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.58/0.80            = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['80', '83'])).
% 0.58/0.80  thf('85', plain,
% 0.58/0.80      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.58/0.80          = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('simplify', [status(thm)], ['84'])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.80  thf('87', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (![X31 : $i]:
% 0.58/0.80         ((r1_yellow_0 @ sk_A @ (sk_E @ X31))
% 0.58/0.80          | ~ (r2_hidden @ X31 @ sk_C)
% 0.58/0.80          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.58/0.80          | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['87', '88'])).
% 0.58/0.80  thf('90', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['86', '89'])).
% 0.58/0.80  thf('91', plain,
% 0.58/0.80      (((r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('simplify', [status(thm)], ['90'])).
% 0.58/0.80  thf('92', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.80  thf('93', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.80  thf('94', plain,
% 0.58/0.80      (![X31 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (sk_E @ X31) @ (k1_zfmisc_1 @ sk_B))
% 0.58/0.80          | ~ (r2_hidden @ X31 @ sk_C)
% 0.58/0.80          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.58/0.80          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.58/0.80             (k1_zfmisc_1 @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['93', '94'])).
% 0.58/0.80  thf('96', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.58/0.80           (k1_zfmisc_1 @ sk_B))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['92', '95'])).
% 0.58/0.80  thf('97', plain,
% 0.58/0.80      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.58/0.80         (k1_zfmisc_1 @ sk_B))
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('simplify', [status(thm)], ['96'])).
% 0.58/0.80  thf('98', plain,
% 0.58/0.80      (![X4 : $i, X5 : $i]:
% 0.58/0.80         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('99', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['97', '98'])).
% 0.58/0.80  thf('100', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.58/0.80         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.58/0.80      inference('split', [status(esa)], ['34'])).
% 0.58/0.80  thf('101', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.58/0.80       ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('split', [status(esa)], ['34'])).
% 0.58/0.80  thf('102', plain, (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['2', '77', '101'])).
% 0.58/0.80  thf('103', plain, ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['100', '102'])).
% 0.58/0.80  thf('104', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t9_yellow_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_orders_2 @ A ) =>
% 0.58/0.80       ( ![B:$i,C:$i]:
% 0.58/0.80         ( ( r1_tarski @ B @ C ) =>
% 0.58/0.80           ( ![D:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.58/0.80                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('105', plain,
% 0.58/0.80      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         (~ (r1_tarski @ X26 @ X27)
% 0.58/0.80          | ~ (r2_lattice3 @ X28 @ X27 @ X29)
% 0.58/0.80          | (r2_lattice3 @ X28 @ X26 @ X29)
% 0.58/0.80          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.58/0.80          | ~ (l1_orders_2 @ X28))),
% 0.58/0.80      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.58/0.80  thf('106', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.58/0.80          | ~ (r1_tarski @ X0 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['104', '105'])).
% 0.58/0.80  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('108', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.58/0.80          | ~ (r1_tarski @ X0 @ X1))),
% 0.58/0.80      inference('demod', [status(thm)], ['106', '107'])).
% 0.58/0.80  thf('109', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (r1_tarski @ X0 @ sk_B) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['103', '108'])).
% 0.58/0.80  thf('110', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['99', '109'])).
% 0.58/0.80  thf('111', plain, (~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.58/0.80  thf('112', plain,
% 0.58/0.80      ((r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2)),
% 0.58/0.80      inference('clc', [status(thm)], ['110', '111'])).
% 0.58/0.80  thf('113', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('114', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X16)
% 0.58/0.80          | (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.58/0.80  thf('115', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.80         (((X14) != (k1_yellow_0 @ X12 @ X13))
% 0.58/0.80          | ~ (r2_lattice3 @ X12 @ X13 @ X15)
% 0.58/0.80          | (r1_orders_2 @ X12 @ X14 @ X15)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.58/0.80          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.58/0.80          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.58/0.80          | ~ (l1_orders_2 @ X12))),
% 0.58/0.80      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.58/0.80  thf('116', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X12)
% 0.58/0.80          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.58/0.80          | ~ (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12))
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.58/0.80          | (r1_orders_2 @ X12 @ (k1_yellow_0 @ X12 @ X13) @ X15)
% 0.58/0.80          | ~ (r2_lattice3 @ X12 @ X13 @ X15))),
% 0.58/0.80      inference('simplify', [status(thm)], ['115'])).
% 0.58/0.80  thf('117', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ X0)
% 0.58/0.80          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.58/0.80          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.58/0.80          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.58/0.80          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.58/0.80          | ~ (l1_orders_2 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['114', '116'])).
% 0.58/0.80  thf('118', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (~ (r1_yellow_0 @ X0 @ X1)
% 0.58/0.80          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.58/0.80          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.58/0.80          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.58/0.80          | ~ (l1_orders_2 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['117'])).
% 0.58/0.80  thf('119', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (l1_orders_2 @ sk_A)
% 0.58/0.80          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2)
% 0.58/0.80          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['113', '118'])).
% 0.58/0.80  thf('120', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('121', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2)
% 0.58/0.80          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['119', '120'])).
% 0.58/0.80  thf('122', plain,
% 0.58/0.80      ((~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.58/0.80        | (r1_orders_2 @ sk_A @ 
% 0.58/0.80           (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.58/0.80           sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['112', '121'])).
% 0.58/0.80  thf('123', plain,
% 0.58/0.80      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.58/0.80        | (r1_orders_2 @ sk_A @ 
% 0.58/0.80           (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.58/0.80           sk_D_2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['91', '122'])).
% 0.58/0.80  thf('124', plain, (~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.58/0.80  thf('125', plain,
% 0.58/0.80      ((r1_orders_2 @ sk_A @ 
% 0.58/0.80        (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ sk_D_2)),
% 0.58/0.80      inference('clc', [status(thm)], ['123', '124'])).
% 0.58/0.80  thf('126', plain,
% 0.58/0.80      (((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 0.58/0.80        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.58/0.80      inference('sup+', [status(thm)], ['85', '125'])).
% 0.58/0.80  thf('127', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.58/0.80          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.58/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.80  thf('128', plain, ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)),
% 0.58/0.80      inference('clc', [status(thm)], ['126', '127'])).
% 0.58/0.80  thf('129', plain, ($false), inference('demod', [status(thm)], ['79', '128'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
