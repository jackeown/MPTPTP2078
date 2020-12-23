%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nNeObJcGyF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:45 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 305 expanded)
%              Number of leaves         :   39 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          : 1975 (9164 expanded)
%              Number of equality atoms :   32 ( 291 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X14 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
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
    ! [X36: $i] :
      ( ( X36
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X36 ) ) )
      | ~ ( r2_hidden @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ sk_C )
      | ( X36
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X36 ) ) ) ) ),
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
    ! [X36: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X36 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ X36 ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_tarski @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r2_lattice3 @ X33 @ X32 @ X34 )
      | ( r2_lattice3 @ X33 @ X31 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k1_yellow_0 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X16 @ X17 @ X19 )
      | ( r1_orders_2 @ X16 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_yellow_0 @ X16 @ X17 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ~ ( r1_yellow_0 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( r1_orders_2 @ X16 @ ( k1_yellow_0 @ X16 @ X17 ) @ X19 )
      | ~ ( r2_lattice3 @ X16 @ X17 @ X19 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X14 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X36: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['38','48'])).

thf('50',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['12','49'])).

thf('51',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['51','56'])).

thf('58',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('63',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X2 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X37: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('69',plain,(
    ! [X11: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('70',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
       != ( k1_yellow_0 @ X16 @ X17 ) )
      | ( r2_lattice3 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_yellow_0 @ X16 @ X17 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ~ ( r1_yellow_0 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ( r2_lattice3 @ X16 @ X17 @ ( k1_yellow_0 @ X16 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('80',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X35 ) @ sk_C )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X11: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('83',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('86',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_orders_2 @ X13 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_D_2 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_C ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('97',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_orders_2 @ X23 @ X22 @ X24 )
      | ~ ( r2_lattice3 @ X23 @ X25 @ X22 )
      | ( r2_lattice3 @ X23 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X3 @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
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
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['78','104'])).

thf('106',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['105'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('108',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B )
                     => ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ B @ D ) ) )
                    & ( ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ B @ D ) )
                     => ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) )
                    & ( ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B )
                     => ( ( r1_orders_2 @ A @ C @ B )
                        & ( r1_orders_2 @ A @ D @ B ) ) )
                    & ( ( ( r1_orders_2 @ A @ C @ B )
                        & ( r1_orders_2 @ A @ D @ B ) )
                     => ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_lattice3 @ X28 @ ( k2_tarski @ X30 @ X29 ) @ X27 )
      | ( r1_orders_2 @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_yellow_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','115'])).

thf('117',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('119',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['117','118'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('120',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('121',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('125',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','59','60','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nNeObJcGyF
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 348 iterations in 0.440s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.89  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.68/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.89  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.68/0.89  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.68/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(sk_E_type, type, sk_E: $i > $i).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.68/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.89  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.68/0.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.89  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.68/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.89  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.68/0.89  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.68/0.89  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.68/0.89  thf(t52_waybel_0, conjecture,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.68/0.89         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89           ( ![C:$i]:
% 0.68/0.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89               ( ( ( ![D:$i]:
% 0.68/0.89                     ( ( ( v1_finset_1 @ D ) & 
% 0.68/0.89                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.68/0.89                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89                         ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 0.68/0.89                   ( ![D:$i]:
% 0.68/0.89                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.68/0.89                            ( ![E:$i]:
% 0.68/0.89                              ( ( ( v1_finset_1 @ E ) & 
% 0.68/0.89                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.68/0.89                                ( ~( ( r1_yellow_0 @ A @ E ) & 
% 0.68/0.89                                     ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.68/0.89                   ( ![D:$i]:
% 0.68/0.89                     ( ( ( v1_finset_1 @ D ) & 
% 0.68/0.89                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.68/0.89                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89                         ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.68/0.89                 ( ![D:$i]:
% 0.68/0.89                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                     ( ( r2_lattice3 @ A @ B @ D ) <=>
% 0.68/0.89                       ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i]:
% 0.68/0.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.68/0.89            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.68/0.89          ( ![B:$i]:
% 0.68/0.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89              ( ![C:$i]:
% 0.68/0.89                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89                  ( ( ( ![D:$i]:
% 0.68/0.89                        ( ( ( v1_finset_1 @ D ) & 
% 0.68/0.89                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.68/0.89                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89                            ( r1_yellow_0 @ A @ D ) ) ) ) & 
% 0.68/0.89                      ( ![D:$i]:
% 0.68/0.89                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.68/0.89                               ( ![E:$i]:
% 0.68/0.89                                 ( ( ( v1_finset_1 @ E ) & 
% 0.68/0.89                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.68/0.89                                   ( ~( ( r1_yellow_0 @ A @ E ) & 
% 0.68/0.89                                        ( ( D ) = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.68/0.89                      ( ![D:$i]:
% 0.68/0.89                        ( ( ( v1_finset_1 @ D ) & 
% 0.68/0.89                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.68/0.89                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89                            ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.68/0.89                    ( ![D:$i]:
% 0.68/0.89                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                        ( ( r2_lattice3 @ A @ B @ D ) <=>
% 0.68/0.89                          ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t52_waybel_0])).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.68/0.89       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.68/0.89      inference('split', [status(esa)], ['0'])).
% 0.68/0.89  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(d9_lattice3, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_orders_2 @ A ) =>
% 0.68/0.89       ( ![B:$i,C:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.68/0.89             ( ![D:$i]:
% 0.68/0.89               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.68/0.89          | (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X14)
% 0.68/0.89          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.68/0.89          | ~ (l1_orders_2 @ X13))),
% 0.68/0.89      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ sk_A)
% 0.68/0.89          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.89  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (![X36 : $i]:
% 0.68/0.89         (((X36) = (k1_yellow_0 @ sk_A @ (sk_E @ X36)))
% 0.68/0.89          | ~ (r2_hidden @ X36 @ sk_C)
% 0.68/0.89          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t4_subset, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.68/0.89       ( m1_subset_1 @ A @ C ) ))).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X8 @ X9)
% 0.68/0.89          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.68/0.89          | (m1_subset_1 @ X8 @ X10))),
% 0.68/0.89      inference('cnf', [status(esa)], [t4_subset])).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      (![X36 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X36 @ sk_C)
% 0.68/0.89          | ((X36) = (k1_yellow_0 @ sk_A @ (sk_E @ X36))))),
% 0.68/0.89      inference('clc', [status(thm)], ['7', '10'])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.68/0.89            = (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['6', '11'])).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      (![X36 : $i]:
% 0.68/0.89         ((m1_subset_1 @ (sk_E @ X36) @ (k1_zfmisc_1 @ sk_B))
% 0.68/0.89          | ~ (r2_hidden @ X36 @ sk_C)
% 0.68/0.89          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X36 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X36 @ sk_C)
% 0.68/0.89          | (m1_subset_1 @ (sk_E @ X36) @ (k1_zfmisc_1 @ sk_B)))),
% 0.68/0.89      inference('clc', [status(thm)], ['14', '15'])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.68/0.89           (k1_zfmisc_1 @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['13', '16'])).
% 0.68/0.89  thf(t3_subset, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i]:
% 0.68/0.89         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89        | (r1_tarski @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('split', [status(esa)], ['20'])).
% 0.68/0.89  thf('22', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t9_yellow_0, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_orders_2 @ A ) =>
% 0.68/0.89       ( ![B:$i,C:$i]:
% 0.68/0.89         ( ( r1_tarski @ B @ C ) =>
% 0.68/0.89           ( ![D:$i]:
% 0.68/0.89             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.68/0.89                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf('23', plain,
% 0.68/0.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X31 @ X32)
% 0.68/0.89          | ~ (r2_lattice3 @ X33 @ X32 @ X34)
% 0.68/0.89          | (r2_lattice3 @ X33 @ X31 @ X34)
% 0.68/0.89          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.68/0.89          | ~ (l1_orders_2 @ X33))),
% 0.68/0.89      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ sk_A)
% 0.68/0.89          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.68/0.89          | ~ (r1_tarski @ X0 @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.89  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.68/0.89          | ~ (r1_tarski @ X0 @ X1))),
% 0.68/0.89      inference('demod', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      ((![X0 : $i]:
% 0.68/0.89          (~ (r1_tarski @ X0 @ sk_B) | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['21', '26'])).
% 0.68/0.89  thf('28', plain,
% 0.68/0.89      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89         | (r2_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.68/0.89            sk_D_2)))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['19', '27'])).
% 0.68/0.89  thf('29', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(dt_k1_yellow_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( l1_orders_2 @ A ) =>
% 0.68/0.89       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X20 : $i, X21 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X20)
% 0.68/0.89          | (m1_subset_1 @ (k1_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.68/0.89  thf(d9_yellow_0, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_orders_2 @ A ) =>
% 0.68/0.89       ( ![B:$i,C:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89           ( ( r1_yellow_0 @ A @ B ) =>
% 0.68/0.89             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.68/0.89               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.68/0.89                 ( ![D:$i]:
% 0.68/0.89                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.68/0.89                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.68/0.89         (((X18) != (k1_yellow_0 @ X16 @ X17))
% 0.68/0.89          | ~ (r2_lattice3 @ X16 @ X17 @ X19)
% 0.68/0.89          | (r1_orders_2 @ X16 @ X18 @ X19)
% 0.68/0.89          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.68/0.89          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.68/0.89          | ~ (r1_yellow_0 @ X16 @ X17)
% 0.68/0.89          | ~ (l1_orders_2 @ X16))),
% 0.68/0.89      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X16)
% 0.68/0.89          | ~ (r1_yellow_0 @ X16 @ X17)
% 0.68/0.89          | ~ (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16))
% 0.68/0.89          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.68/0.89          | (r1_orders_2 @ X16 @ (k1_yellow_0 @ X16 @ X17) @ X19)
% 0.68/0.89          | ~ (r2_lattice3 @ X16 @ X17 @ X19))),
% 0.68/0.89      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X0)
% 0.68/0.89          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.68/0.89          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.68/0.89          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.89          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.68/0.89          | ~ (l1_orders_2 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['30', '32'])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (r1_yellow_0 @ X0 @ X1)
% 0.68/0.89          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.89          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.68/0.89          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.68/0.89          | ~ (l1_orders_2 @ X0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['33'])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ sk_A)
% 0.68/0.89          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2)
% 0.68/0.89          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['29', '34'])).
% 0.68/0.89  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('37', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2)
% 0.68/0.89          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.89  thf('38', plain,
% 0.68/0.89      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89         | ~ (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.68/0.89         | (r1_orders_2 @ sk_A @ 
% 0.68/0.89            (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.68/0.89            sk_D_2)))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['28', '37'])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf('40', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.68/0.89          | (m1_subset_1 @ (sk_D @ X12 @ X14 @ X13) @ (u1_struct_0 @ X13))
% 0.68/0.89          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.68/0.89          | ~ (l1_orders_2 @ X13))),
% 0.68/0.89      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.68/0.89  thf('42', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ sk_A)
% 0.68/0.89          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.68/0.89  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['42', '43'])).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      (![X36 : $i]:
% 0.68/0.89         ((r1_yellow_0 @ sk_A @ (sk_E @ X36))
% 0.68/0.89          | ~ (r2_hidden @ X36 @ sk_C)
% 0.68/0.89          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.68/0.89          | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89        | (r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.68/0.89        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.68/0.89      inference('sup-', [status(thm)], ['39', '46'])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      (((r1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.68/0.89        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.68/0.89      inference('simplify', [status(thm)], ['47'])).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      ((((r1_orders_2 @ sk_A @ 
% 0.68/0.89          (k1_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))) @ 
% 0.68/0.89          sk_D_2)
% 0.68/0.89         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('clc', [status(thm)], ['38', '48'])).
% 0.68/0.89  thf('50', plain,
% 0.68/0.89      ((((r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 0.68/0.89         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89         | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['12', '49'])).
% 0.68/0.89  thf('51', plain,
% 0.68/0.89      ((((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.68/0.89         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['50'])).
% 0.68/0.89  thf('52', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('53', plain,
% 0.68/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.68/0.89          | ~ (r1_orders_2 @ X13 @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.68/0.89          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.68/0.89          | ~ (l1_orders_2 @ X13))),
% 0.68/0.89      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.68/0.89  thf('54', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ sk_A)
% 0.68/0.89          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.68/0.89      inference('sup-', [status(thm)], ['52', '53'])).
% 0.68/0.89  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('56', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.68/0.89      inference('demod', [status(thm)], ['54', '55'])).
% 0.68/0.89  thf('57', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.89      inference('clc', [status(thm)], ['51', '56'])).
% 0.68/0.89  thf('58', plain,
% 0.68/0.89      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.68/0.89         <= (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.89      inference('split', [status(esa)], ['0'])).
% 0.68/0.89  thf('59', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.68/0.89       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.68/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.68/0.89  thf('60', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.68/0.89       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.68/0.89      inference('split', [status(esa)], ['20'])).
% 0.68/0.89  thf('61', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['42', '43'])).
% 0.68/0.89  thf('62', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf(l1_zfmisc_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.68/0.89  thf('63', plain,
% 0.68/0.89      (![X2 : $i, X4 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X2) @ X4) | ~ (r2_hidden @ X2 @ X4))),
% 0.68/0.89      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.89  thf('64', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (r1_tarski @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['62', '63'])).
% 0.68/0.89  thf('65', plain,
% 0.68/0.89      (![X5 : $i, X7 : $i]:
% 0.68/0.89         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.89  thf('66', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.68/0.89             (k1_zfmisc_1 @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.68/0.89  thf('67', plain,
% 0.68/0.89      (![X37 : $i]:
% 0.68/0.89         (((X37) = (k1_xboole_0))
% 0.68/0.89          | (r1_yellow_0 @ sk_A @ X37)
% 0.68/0.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ sk_B))
% 0.68/0.89          | ~ (v1_finset_1 @ X37))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('68', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.89        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.68/0.89        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.68/0.89        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['66', '67'])).
% 0.68/0.89  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.68/0.89  thf('69', plain, (![X11 : $i]: (v1_finset_1 @ (k1_tarski @ X11))),
% 0.68/0.89      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.68/0.89  thf('70', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.89        | (r1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.68/0.89        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['68', '69'])).
% 0.68/0.89  thf('71', plain,
% 0.68/0.89      (![X20 : $i, X21 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X20)
% 0.68/0.89          | (m1_subset_1 @ (k1_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.68/0.89  thf('72', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.89         (((X18) != (k1_yellow_0 @ X16 @ X17))
% 0.68/0.89          | (r2_lattice3 @ X16 @ X17 @ X18)
% 0.68/0.89          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.68/0.89          | ~ (r1_yellow_0 @ X16 @ X17)
% 0.68/0.89          | ~ (l1_orders_2 @ X16))),
% 0.68/0.89      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.68/0.89  thf('73', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X16)
% 0.68/0.89          | ~ (r1_yellow_0 @ X16 @ X17)
% 0.68/0.89          | ~ (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16))
% 0.68/0.89          | (r2_lattice3 @ X16 @ X17 @ (k1_yellow_0 @ X16 @ X17)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['72'])).
% 0.68/0.89  thf('74', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X0)
% 0.68/0.89          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.68/0.89          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.68/0.89          | ~ (l1_orders_2 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['71', '73'])).
% 0.68/0.89  thf('75', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r1_yellow_0 @ X0 @ X1)
% 0.68/0.89          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.68/0.89          | ~ (l1_orders_2 @ X0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['74'])).
% 0.68/0.89  thf('76', plain,
% 0.68/0.89      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.89        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.89        | ~ (l1_orders_2 @ sk_A)
% 0.68/0.89        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.68/0.89           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['70', '75'])).
% 0.68/0.89  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('78', plain,
% 0.68/0.89      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.89        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.89        | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.68/0.89           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.68/0.89      inference('demod', [status(thm)], ['76', '77'])).
% 0.68/0.89  thf('79', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.89          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.68/0.89             (k1_zfmisc_1 @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.68/0.89  thf('80', plain,
% 0.68/0.89      (![X35 : $i]:
% 0.68/0.89         (((X35) = (k1_xboole_0))
% 0.68/0.89          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X35) @ sk_C)
% 0.68/0.89          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ sk_B))
% 0.68/0.89          | ~ (v1_finset_1 @ X35))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('81', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.89        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.68/0.89        | (r2_hidden @ 
% 0.68/0.89           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.68/0.89           sk_C)
% 0.68/0.89        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['79', '80'])).
% 0.68/0.89  thf('82', plain, (![X11 : $i]: (v1_finset_1 @ (k1_tarski @ X11))),
% 0.68/0.89      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.68/0.89  thf('83', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.89        | (r2_hidden @ 
% 0.68/0.89           (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.68/0.89           sk_C)
% 0.68/0.89        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['81', '82'])).
% 0.68/0.89  thf('84', plain,
% 0.68/0.89      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.68/0.89         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.89      inference('split', [status(esa)], ['20'])).
% 0.68/0.89  thf('85', plain,
% 0.68/0.89      (![X20 : $i, X21 : $i]:
% 0.68/0.89         (~ (l1_orders_2 @ X20)
% 0.68/0.89          | (m1_subset_1 @ (k1_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.68/0.89  thf('86', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('87', plain,
% 0.68/0.89      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.68/0.90          | ~ (r2_lattice3 @ X13 @ X14 @ X12)
% 0.68/0.90          | ~ (r2_hidden @ X15 @ X14)
% 0.68/0.90          | (r1_orders_2 @ X13 @ X15 @ X12)
% 0.68/0.90          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.68/0.90          | ~ (l1_orders_2 @ X13))),
% 0.68/0.90      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.68/0.90  thf('88', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (l1_orders_2 @ sk_A)
% 0.68/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90          | ~ (r2_hidden @ X0 @ X1)
% 0.68/0.90          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['86', '87'])).
% 0.68/0.90  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('90', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90          | ~ (r2_hidden @ X0 @ X1)
% 0.68/0.90          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.68/0.90      inference('demod', [status(thm)], ['88', '89'])).
% 0.68/0.90  thf('91', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (l1_orders_2 @ sk_A)
% 0.68/0.90          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.68/0.90          | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.68/0.90          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['85', '90'])).
% 0.68/0.90  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('93', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.68/0.90          | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.68/0.90          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2))),
% 0.68/0.90      inference('demod', [status(thm)], ['91', '92'])).
% 0.68/0.90  thf('94', plain,
% 0.68/0.90      ((![X0 : $i]:
% 0.68/0.90          ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ sk_D_2)
% 0.68/0.90           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_C)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['84', '93'])).
% 0.68/0.90  thf('95', plain,
% 0.68/0.90      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90         | (r1_orders_2 @ sk_A @ 
% 0.68/0.90            (k1_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.68/0.90            sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['83', '94'])).
% 0.68/0.90  thf('96', plain,
% 0.68/0.90      (![X20 : $i, X21 : $i]:
% 0.68/0.90         (~ (l1_orders_2 @ X20)
% 0.68/0.90          | (m1_subset_1 @ (k1_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.68/0.90  thf(t4_yellow_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.90               ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.68/0.90                 ( ![D:$i]:
% 0.68/0.90                   ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.68/0.90                       ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.68/0.90                     ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.68/0.90                       ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('97', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.68/0.90          | ~ (r1_orders_2 @ X23 @ X22 @ X24)
% 0.68/0.90          | ~ (r2_lattice3 @ X23 @ X25 @ X22)
% 0.68/0.90          | (r2_lattice3 @ X23 @ X25 @ X24)
% 0.68/0.90          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.68/0.90          | ~ (l1_orders_2 @ X23)
% 0.68/0.90          | ~ (v4_orders_2 @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_yellow_0])).
% 0.68/0.90  thf('98', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.90         (~ (l1_orders_2 @ X0)
% 0.68/0.90          | ~ (v4_orders_2 @ X0)
% 0.68/0.90          | ~ (l1_orders_2 @ X0)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.90          | (r2_lattice3 @ X0 @ X3 @ X2)
% 0.68/0.90          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.68/0.90          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['96', '97'])).
% 0.68/0.90  thf('99', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.90         (~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.68/0.90          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.68/0.90          | (r2_lattice3 @ X0 @ X3 @ X2)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.90          | ~ (v4_orders_2 @ X0)
% 0.68/0.90          | ~ (l1_orders_2 @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['98'])).
% 0.68/0.90  thf('100', plain,
% 0.68/0.90      ((![X0 : $i]:
% 0.68/0.90          ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90           | ~ (l1_orders_2 @ sk_A)
% 0.68/0.90           | ~ (v4_orders_2 @ sk_A)
% 0.68/0.90           | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.68/0.90           | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90           | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.68/0.90                (k1_yellow_0 @ sk_A @ 
% 0.68/0.90                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['95', '99'])).
% 0.68/0.90  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('102', plain, ((v4_orders_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('103', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('104', plain,
% 0.68/0.90      ((![X0 : $i]:
% 0.68/0.90          ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90           | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90           | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.68/0.90                (k1_yellow_0 @ sk_A @ 
% 0.68/0.90                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.68/0.90  thf('105', plain,
% 0.68/0.90      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | (r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.68/0.90            sk_D_2)
% 0.68/0.90         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['78', '104'])).
% 0.68/0.90  thf('106', plain,
% 0.68/0.90      ((((r2_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.68/0.90          sk_D_2)
% 0.68/0.90         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('simplify', [status(thm)], ['105'])).
% 0.68/0.90  thf(t69_enumset1, axiom,
% 0.68/0.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.68/0.90  thf('107', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.68/0.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.90  thf('108', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(t8_yellow_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( l1_orders_2 @ A ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.90               ( ![D:$i]:
% 0.68/0.90                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.90                   ( ( ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) =>
% 0.68/0.90                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.68/0.90                         ( r1_orders_2 @ A @ B @ D ) ) ) & 
% 0.68/0.90                     ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.68/0.90                         ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.68/0.90                       ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) & 
% 0.68/0.90                     ( ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) =>
% 0.68/0.90                       ( ( r1_orders_2 @ A @ C @ B ) & 
% 0.68/0.90                         ( r1_orders_2 @ A @ D @ B ) ) ) & 
% 0.68/0.90                     ( ( ( r1_orders_2 @ A @ C @ B ) & 
% 0.68/0.90                         ( r1_orders_2 @ A @ D @ B ) ) =>
% 0.68/0.90                       ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('109', plain,
% 0.68/0.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.68/0.90          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.68/0.90          | ~ (r2_lattice3 @ X28 @ (k2_tarski @ X30 @ X29) @ X27)
% 0.68/0.90          | (r1_orders_2 @ X28 @ X29 @ X27)
% 0.68/0.90          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.68/0.90          | ~ (l1_orders_2 @ X28))),
% 0.68/0.90      inference('cnf', [status(esa)], [t8_yellow_0])).
% 0.68/0.90  thf('110', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (l1_orders_2 @ sk_A)
% 0.68/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | (r1_orders_2 @ sk_A @ X1 @ sk_D_2)
% 0.68/0.90          | ~ (r2_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_D_2)
% 0.68/0.90          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['108', '109'])).
% 0.68/0.90  thf('111', plain, ((l1_orders_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('112', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | (r1_orders_2 @ sk_A @ X1 @ sk_D_2)
% 0.68/0.90          | ~ (r2_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_D_2)
% 0.68/0.90          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.90      inference('demod', [status(thm)], ['110', '111'])).
% 0.68/0.90  thf('113', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2)
% 0.68/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['107', '112'])).
% 0.68/0.90  thf('114', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.68/0.90      inference('simplify', [status(thm)], ['113'])).
% 0.68/0.90  thf('115', plain,
% 0.68/0.90      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.68/0.90              (u1_struct_0 @ sk_A))
% 0.68/0.90         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['106', '114'])).
% 0.68/0.90  thf('116', plain,
% 0.68/0.90      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.68/0.90         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['61', '115'])).
% 0.68/0.90  thf('117', plain,
% 0.68/0.90      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.68/0.90         | (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.68/0.90         | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('simplify', [status(thm)], ['116'])).
% 0.68/0.90  thf('118', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.68/0.90          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.68/0.90      inference('demod', [status(thm)], ['54', '55'])).
% 0.68/0.90  thf('119', plain,
% 0.68/0.90      ((((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.68/0.90         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('clc', [status(thm)], ['117', '118'])).
% 0.68/0.90  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.68/0.90  thf('120', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.68/0.90  thf('121', plain,
% 0.68/0.90      (((~ (v1_xboole_0 @ k1_xboole_0) | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['119', '120'])).
% 0.68/0.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.68/0.90  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.68/0.90  thf('123', plain,
% 0.68/0.90      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.68/0.90         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.68/0.90      inference('demod', [status(thm)], ['121', '122'])).
% 0.68/0.90  thf('124', plain,
% 0.68/0.90      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.68/0.90         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.68/0.90      inference('split', [status(esa)], ['0'])).
% 0.68/0.90  thf('125', plain,
% 0.68/0.90      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.68/0.90       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['123', '124'])).
% 0.68/0.90  thf('126', plain, ($false),
% 0.68/0.90      inference('sat_resolution*', [status(thm)], ['1', '59', '60', '125'])).
% 0.68/0.90  
% 0.68/0.90  % SZS output end Refutation
% 0.68/0.90  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
