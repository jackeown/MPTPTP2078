%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1673+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VSwGCNqsXt

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:58 EST 2020

% Result     : Theorem 6.60s
% Output     : Refutation 6.60s
% Verified   : 
% Statistics : Number of formulae       : 2005 (6411852625698543894528 expanded)
%              Number of leaves         :   55 (1747661021555333267456 expanded)
%              Depth                    :  473
%              Number of atoms          : 50569 (227084212227197846421504 expanded)
%              Number of equality atoms : 1456 (5976247090459302690816 expanded)
%              Maximal formula depth    :   24 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_6_type,type,(
    zip_tseitin_6: $i > $i > $o )).

thf(zip_tseitin_8_type,type,(
    zip_tseitin_8: $i > $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_7_type,type,(
    zip_tseitin_7: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(t53_waybel_0,conjecture,(
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
               => ( ( r1_yellow_0 @ A @ B )
                <=> ( r1_yellow_0 @ A @ C ) ) ) ) ) ) )).

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
                 => ( ( r1_yellow_0 @ A @ B )
                  <=> ( r1_yellow_0 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_waybel_0])).

thf('0',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t46_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                <=> ( r2_lattice3 @ A @ C @ D ) ) )
            & ( r1_yellow_0 @ A @ B ) )
         => ( r1_yellow_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v3_orders_2 @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) )
                        & ( v1_finset_1 @ D ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ! [E: $i] :
                              ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                                & ( v1_finset_1 @ E ) )
                             => ~ ( ( D
                                    = ( k1_yellow_0 @ A @ E ) )
                                  & ( r1_yellow_0 @ A @ E ) ) )
                          & ( r2_hidden @ D @ C ) ) )
                  & ! [D: $i] :
                      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) )
                        & ( v1_finset_1 @ D ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r1_yellow_0 @ A @ D ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                    <=> ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ B )
       => ( zip_tseitin_1 @ D @ C @ A ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ~ ( zip_tseitin_3 @ D @ C @ B @ A ) )
     => ( zip_tseitin_4 @ D @ C @ B @ A ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(zf_stmt_3,axiom,(
    ! [D: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_5 @ D @ B )
       => ( zip_tseitin_6 @ D @ A ) )
     => ( zip_tseitin_7 @ D @ B @ A ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ( zip_tseitin_5 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_4,type,(
    zip_tseitin_8: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_8 @ D @ C @ B @ A )
     => ( ( r2_lattice3 @ A @ B @ D )
      <=> ( r2_lattice3 @ A @ C @ D ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_7: $i > $i > $i > $o )).

thf(zf_stmt_7,type,(
    zip_tseitin_6: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,A: $i] :
      ( ( ( D != k1_xboole_0 )
       => ( r1_yellow_0 @ A @ D ) )
     => ( zip_tseitin_6 @ D @ A ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_5 @ D @ B )
     => ( ( v1_finset_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_12,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
     => ( ( r2_hidden @ D @ C )
        & ! [E: $i] :
            ( ( ( v1_finset_1 @ E )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
           => ~ ( ( r1_yellow_0 @ A @ E )
                & ( D
                  = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_14,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_15,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_16,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( ( D != k1_xboole_0 )
       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) )
     => ( zip_tseitin_1 @ D @ C @ A ) ) )).

thf(zf_stmt_17,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_18,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ B )
     => ( ( v1_finset_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_19,axiom,(
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
                      ( zip_tseitin_7 @ D @ B @ A )
                  & ! [D: $i] :
                      ( zip_tseitin_4 @ D @ C @ B @ A )
                  & ! [D: $i] :
                      ( zip_tseitin_2 @ D @ C @ B @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( zip_tseitin_8 @ D @ C @ B @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ X35 @ X36 ) @ X35 @ X36 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( zip_tseitin_8 @ X38 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_19])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('64',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('70',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('73',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('87',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('88',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('93',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('94',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('99',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('100',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_finset_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ( X15
       != ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('105',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['91','108'])).

thf('110',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['85','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','116'])).

thf('118',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['113'])).

thf('120',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('126',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('129',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('134',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['131'])).

thf('136',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('137',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('139',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('140',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('145',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','152'])).

thf('156',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('163',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['160'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('169',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('172',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['166','173'])).

thf('175',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('178',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('184',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('185',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['183','186'])).

thf('188',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('190',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('191',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('194',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('196',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('197',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['195','198'])).

thf('200',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('202',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['194','202'])).

thf('204',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['188','204'])).

thf('206',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['182','206'])).

thf('208',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['153','208'])).

thf('210',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('212',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','212'])).

thf('214',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['209'])).

thf('216',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('217',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['214','217'])).

thf('219',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['213'])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('222',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('225',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['219','226'])).

thf('228',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_finset_1 @ X24 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('230',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('232',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('234',plain,(
    ! [X9: $i,X10: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X9 @ X10 ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('236',plain,(
    ! [X9: $i,X10: $i] :
      ( zip_tseitin_1 @ o_0_0_xboole_0 @ X9 @ X10 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('238',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ! [X0: $i] :
        ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['232','238','239'])).

thf('241',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','241'])).

thf('243',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('244',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','241'])).

thf('245',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('246',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('248',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['243','248'])).

thf('250',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('252',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('253',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['250','253'])).

thf('255',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['249'])).

thf('257',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('258',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('261',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['255','262'])).

thf('264',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['263'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('267',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['264','269'])).

thf('271',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['263'])).

thf('273',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('274',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['272','275'])).

thf('277',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['263'])).

thf('279',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('280',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['278','281'])).

thf('283',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['263'])).

thf('285',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('286',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['284','287'])).

thf('289',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('291',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['283','291'])).

thf('293',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['277','293'])).

thf('295',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['271','295'])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['242','297'])).

thf('299',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','301'])).

thf('303',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['298'])).

thf('305',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('306',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['303','306'])).

thf('308',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['302'])).

thf('310',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('311',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('314',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['311','312','313'])).

thf('315',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['308','315'])).

thf('317',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_finset_1 @ X24 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('319',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['227'])).

thf('324',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('325',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    ! [X41: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('328',plain,(
    ! [X41: $i] :
      ( ( X41 = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('329',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['325','328'])).

thf('330',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['322','329'])).

thf('331',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ~ ( r1_yellow_0 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('333',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_6 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('335',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('337',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['335','336'])).

thf('338',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','338'])).

thf('340',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','339'])).

thf('341',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','340'])).

thf('342',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','341'])).

thf('343',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('344',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','341'])).

thf('345',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('346',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('347',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('348',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['346','347'])).

thf('349',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['343','348'])).

thf('350',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('352',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('353',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['350','353'])).

thf('355',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['349'])).

thf('357',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('358',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('361',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['358','359','360'])).

thf('362',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['355','362'])).

thf('364',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['363'])).

thf('366',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('367',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('368',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['364','369'])).

thf('371',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['363'])).

thf('373',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('374',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['373','374'])).

thf('376',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['372','375'])).

thf('377',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['376'])).

thf('378',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['363'])).

thf('379',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('380',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['378','381'])).

thf('383',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['363'])).

thf('385',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('386',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['385','386'])).

thf('388',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['384','387'])).

thf('389',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['388'])).

thf('390',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('391',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['389','390'])).

thf('392',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['383','391'])).

thf('393',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['392'])).

thf('394',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['377','393'])).

thf('395',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['394'])).

thf('396',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['371','395'])).

thf('397',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['396'])).

thf('398',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['342','397'])).

thf('399',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['398'])).

thf('400',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('401',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['399','400'])).

thf('402',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','401'])).

thf('403',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['402'])).

thf('404',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['398'])).

thf('405',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('406',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['404','405'])).

thf('407',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['403','406'])).

thf('408',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['402'])).

thf('410',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('411',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['409','410'])).

thf('412',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('413',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('414',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['411','412','413'])).

thf('415',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['414'])).

thf('416',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['408','415'])).

thf('417',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('419',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['416'])).

thf('421',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('422',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['420','421'])).

thf('423',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('424',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['422','423'])).

thf('425',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['424'])).

thf('426',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['419','425'])).

thf('427',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('429',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['427','428'])).

thf('430',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('431',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['429','430'])).

thf('432',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['337'])).

thf('433',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['431','432'])).

thf('434',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['433','434'])).

thf('436',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['435'])).

thf('437',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','436'])).

thf('438',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','437'])).

thf('439',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('440',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','437'])).

thf('441',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('442',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['440','441'])).

thf('443',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('444',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['442','443'])).

thf('445',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['439','444'])).

thf('446',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['445'])).

thf('447',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['440','441'])).

thf('448',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('449',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['447','448'])).

thf('450',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['446','449'])).

thf('451',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['450'])).

thf('452',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['445'])).

thf('453',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('454',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['452','453'])).

thf('455',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('456',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('457',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['454','455','456'])).

thf('458',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['457'])).

thf('459',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['451','458'])).

thf('460',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['459'])).

thf('461',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['459'])).

thf('462',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('463',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('464',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('465',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['463','464'])).

thf('466',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['460','465'])).

thf('467',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['466'])).

thf('468',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['459'])).

thf('469',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('470',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('471',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['469','470'])).

thf('472',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['468','471'])).

thf('473',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['472'])).

thf('474',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['459'])).

thf('475',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('476',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['475','476'])).

thf('478',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['474','477'])).

thf('479',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['478'])).

thf('480',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['459'])).

thf('481',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('482',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('483',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['481','482'])).

thf('484',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['480','483'])).

thf('485',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['484'])).

thf('486',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('487',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['485','486'])).

thf('488',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['479','487'])).

thf('489',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['488'])).

thf('490',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['473','489'])).

thf('491',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['490'])).

thf('492',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['467','491'])).

thf('493',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['492'])).

thf('494',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['438','493'])).

thf('495',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['494'])).

thf('496',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('497',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['495','496'])).

thf('498',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','497'])).

thf('499',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['498'])).

thf('500',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['494'])).

thf('501',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('502',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['500','501'])).

thf('503',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['499','502'])).

thf('504',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['503'])).

thf('505',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['498'])).

thf('506',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('507',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['505','506'])).

thf('508',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('510',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['507','508','509'])).

thf('511',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['510'])).

thf('512',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['504','511'])).

thf('513',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['512'])).

thf('514',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['320','321'])).

thf('515',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('516',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('517',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['512'])).

thf('518',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('519',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['517','518'])).

thf('520',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('521',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('522',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['519','520','521'])).

thf('523',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['522'])).

thf('524',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['516','523'])).

thf('525',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('526',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['516','523'])).

thf('527',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('528',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['526','527'])).

thf('529',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('530',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['528','529'])).

thf('531',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['525','530'])).

thf('532',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['531'])).

thf('533',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['526','527'])).

thf('534',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('535',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['533','534'])).

thf('536',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['532','535'])).

thf('537',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['536'])).

thf('538',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['531'])).

thf('539',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('540',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['538','539'])).

thf('541',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('542',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('543',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['540','541','542'])).

thf('544',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['543'])).

thf('545',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['537','544'])).

thf('546',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['545'])).

thf('547',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['545'])).

thf('548',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('549',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('550',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('551',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['549','550'])).

thf('552',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['546','551'])).

thf('553',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['552'])).

thf('554',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['545'])).

thf('555',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('556',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('557',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['555','556'])).

thf('558',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['554','557'])).

thf('559',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['558'])).

thf('560',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['545'])).

thf('561',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('562',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('563',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['561','562'])).

thf('564',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['560','563'])).

thf('565',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['564'])).

thf('566',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['545'])).

thf('567',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('568',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('569',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['567','568'])).

thf('570',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['566','569'])).

thf('571',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['570'])).

thf('572',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('573',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['571','572'])).

thf('574',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['565','573'])).

thf('575',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['574'])).

thf('576',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['559','575'])).

thf('577',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['576'])).

thf('578',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['553','577'])).

thf('579',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['578'])).

thf('580',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['524','579'])).

thf('581',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['580'])).

thf('582',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('583',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['581','582'])).

thf('584',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['515','583'])).

thf('585',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['584'])).

thf('586',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['580'])).

thf('587',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('588',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['586','587'])).

thf('589',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['585','588'])).

thf('590',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['589'])).

thf('591',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['584'])).

thf('592',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('593',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['591','592'])).

thf('594',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('595',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('596',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['593','594','595'])).

thf('597',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['596'])).

thf('598',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['590','597'])).

thf('599',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['598'])).

thf('600',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('601',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['599','600'])).

thf('602',plain,(
    ! [X41: $i] :
      ( ( X41 = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('603',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['601','602'])).

thf('604',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['603'])).

thf('605',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['514','604'])).

thf('606',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['605'])).

thf('607',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ~ ( r1_yellow_0 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('608',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_6 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['606','607'])).

thf('609',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('610',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['608','609'])).

thf('611',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('612',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['610','611'])).

thf('613',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['612'])).

thf('614',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['513','613'])).

thf('615',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('616',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('617',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['614','615','616'])).

thf('618',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['617'])).

thf('619',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','618'])).

thf('620',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','619'])).

thf('621',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('622',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','619'])).

thf('623',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('624',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['622','623'])).

thf('625',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('626',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['624','625'])).

thf('627',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['621','626'])).

thf('628',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['627'])).

thf('629',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['622','623'])).

thf('630',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('631',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['629','630'])).

thf('632',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['628','631'])).

thf('633',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['632'])).

thf('634',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['627'])).

thf('635',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('636',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['634','635'])).

thf('637',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('638',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('639',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['636','637','638'])).

thf('640',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['639'])).

thf('641',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['633','640'])).

thf('642',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['641'])).

thf('643',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['641'])).

thf('644',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('645',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['643','644'])).

thf('646',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('647',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['645','646'])).

thf('648',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['642','647'])).

thf('649',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['648'])).

thf('650',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['641'])).

thf('651',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['643','644'])).

thf('652',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('653',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['651','652'])).

thf('654',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['650','653'])).

thf('655',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['654'])).

thf('656',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['641'])).

thf('657',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['643','644'])).

thf('658',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('659',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['657','658'])).

thf('660',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['656','659'])).

thf('661',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['660'])).

thf('662',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['641'])).

thf('663',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['643','644'])).

thf('664',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('665',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['663','664'])).

thf('666',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['662','665'])).

thf('667',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['666'])).

thf('668',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('669',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['667','668'])).

thf('670',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['661','669'])).

thf('671',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['670'])).

thf('672',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['655','671'])).

thf('673',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['672'])).

thf('674',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['649','673'])).

thf('675',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['674'])).

thf('676',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['620','675'])).

thf('677',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['676'])).

thf('678',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('679',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['677','678'])).

thf('680',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','679'])).

thf('681',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['680'])).

thf('682',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['676'])).

thf('683',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('684',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['682','683'])).

thf('685',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['681','684'])).

thf('686',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['685'])).

thf('687',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['680'])).

thf('688',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('689',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['687','688'])).

thf('690',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('691',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('692',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['689','690','691'])).

thf('693',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['692'])).

thf('694',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['686','693'])).

thf('695',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['694'])).

thf('696',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('697',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['695','696'])).

thf('698',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('699',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_7 @ o_0_0_xboole_0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['697','698'])).

thf('700',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('701',plain,(
    ! [X27: $i] :
      ( zip_tseitin_6 @ k1_xboole_0 @ X27 ) ),
    inference(simplify,[status(thm)],['700'])).

thf('702',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('703',plain,(
    ! [X27: $i] :
      ( zip_tseitin_6 @ o_0_0_xboole_0 @ X27 ) ),
    inference(demod,[status(thm)],['701','702'])).

thf('704',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('705',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_7 @ o_0_0_xboole_0 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['703','704'])).

thf('706',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['699','705'])).

thf('707',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','706'])).

thf('708',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','707'])).

thf('709',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','708'])).

thf('710',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','709'])).

thf('711',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('712',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','709'])).

thf('713',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('714',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['712','713'])).

thf('715',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('716',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['714','715'])).

thf('717',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['711','716'])).

thf('718',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['717'])).

thf('719',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['712','713'])).

thf('720',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('721',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['719','720'])).

thf('722',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['718','721'])).

thf('723',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['722'])).

thf('724',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['717'])).

thf('725',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('726',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['724','725'])).

thf('727',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('728',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('729',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['726','727','728'])).

thf('730',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['729'])).

thf('731',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['723','730'])).

thf('732',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['731'])).

thf('733',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['731'])).

thf('734',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('735',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['733','734'])).

thf('736',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('737',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['735','736'])).

thf('738',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['732','737'])).

thf('739',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['738'])).

thf('740',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['731'])).

thf('741',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['733','734'])).

thf('742',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('743',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['741','742'])).

thf('744',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['740','743'])).

thf('745',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['744'])).

thf('746',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['731'])).

thf('747',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['733','734'])).

thf('748',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('749',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['747','748'])).

thf('750',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['746','749'])).

thf('751',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['750'])).

thf('752',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['731'])).

thf('753',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['733','734'])).

thf('754',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('755',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['753','754'])).

thf('756',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['752','755'])).

thf('757',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['756'])).

thf('758',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('759',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['757','758'])).

thf('760',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['751','759'])).

thf('761',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['760'])).

thf('762',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['745','761'])).

thf('763',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['762'])).

thf('764',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['739','763'])).

thf('765',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['764'])).

thf('766',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['710','765'])).

thf('767',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['766'])).

thf('768',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('769',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['767','768'])).

thf('770',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','769'])).

thf('771',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['770'])).

thf('772',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['766'])).

thf('773',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('774',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['772','773'])).

thf('775',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['771','774'])).

thf('776',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['775'])).

thf('777',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['770'])).

thf('778',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('779',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['777','778'])).

thf('780',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('781',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('782',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['779','780','781'])).

thf('783',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['782'])).

thf('784',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['776','783'])).

thf('785',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['784'])).

thf('786',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('787',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['785','786'])).

thf('788',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('789',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['787','788'])).

thf('790',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['785','786'])).

thf('791',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('792',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['790','791'])).

thf('793',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('794',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['792','793'])).

thf('795',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['789','794'])).

thf('796',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['795'])).

thf('797',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('798',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['796','797'])).

thf('799',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('800',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['798','799'])).

thf('801',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','706'])).

thf('802',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['800','801'])).

thf('803',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('804',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['802','803'])).

thf('805',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['804'])).

thf('806',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','805'])).

thf('807',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('808',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','805'])).

thf('809',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('810',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['808','809'])).

thf('811',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('812',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['810','811'])).

thf('813',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['807','812'])).

thf('814',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['813'])).

thf('815',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['808','809'])).

thf('816',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('817',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['815','816'])).

thf('818',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['814','817'])).

thf('819',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['818'])).

thf('820',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['813'])).

thf('821',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('822',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['820','821'])).

thf('823',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('824',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('825',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['822','823','824'])).

thf('826',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['825'])).

thf('827',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['819','826'])).

thf('828',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['827'])).

thf('829',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['827'])).

thf('830',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('831',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['829','830'])).

thf('832',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('833',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['831','832'])).

thf('834',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['828','833'])).

thf('835',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['834'])).

thf('836',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['827'])).

thf('837',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['829','830'])).

thf('838',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('839',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['837','838'])).

thf('840',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['836','839'])).

thf('841',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['840'])).

thf('842',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['827'])).

thf('843',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['829','830'])).

thf('844',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('845',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['843','844'])).

thf('846',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['842','845'])).

thf('847',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['846'])).

thf('848',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['827'])).

thf('849',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['829','830'])).

thf('850',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('851',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['849','850'])).

thf('852',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['848','851'])).

thf('853',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['852'])).

thf('854',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('855',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['853','854'])).

thf('856',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['847','855'])).

thf('857',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['856'])).

thf('858',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['841','857'])).

thf('859',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['858'])).

thf('860',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['835','859'])).

thf('861',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['860'])).

thf('862',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['806','861'])).

thf('863',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['862'])).

thf('864',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('865',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['863','864'])).

thf('866',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','865'])).

thf('867',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['866'])).

thf('868',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['862'])).

thf('869',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('870',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['868','869'])).

thf('871',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['867','870'])).

thf('872',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['871'])).

thf('873',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['866'])).

thf('874',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('875',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['873','874'])).

thf('876',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('877',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('878',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['875','876','877'])).

thf('879',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['878'])).

thf('880',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['872','879'])).

thf('881',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['880'])).

thf('882',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('883',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['881','882'])).

thf('884',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','706'])).

thf('885',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['883','884'])).

thf('886',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('887',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('888',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['885','886','887'])).

thf('889',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['888'])).

thf('890',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','889'])).

thf('891',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('892',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','889'])).

thf('893',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('894',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['892','893'])).

thf('895',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('896',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['894','895'])).

thf('897',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['891','896'])).

thf('898',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['897'])).

thf('899',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['892','893'])).

thf('900',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('901',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['899','900'])).

thf('902',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['898','901'])).

thf('903',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['902'])).

thf('904',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['897'])).

thf('905',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('906',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['904','905'])).

thf('907',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('908',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('909',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['906','907','908'])).

thf('910',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['909'])).

thf('911',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['903','910'])).

thf('912',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['911'])).

thf('913',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('914',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['912','913'])).

thf('915',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('916',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['914','915'])).

thf('917',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('918',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['916','917'])).

thf('919',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['912','913'])).

thf('920',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['918','919'])).

thf('921',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['914','915'])).

thf('922',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('923',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['921','922'])).

thf('924',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['912','913'])).

thf('925',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['923','924'])).

thf('926',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['914','915'])).

thf('927',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('928',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['926','927'])).

thf('929',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['912','913'])).

thf('930',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['928','929'])).

thf('931',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['914','915'])).

thf('932',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('933',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['931','932'])).

thf('934',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['912','913'])).

thf('935',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['933','934'])).

thf('936',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('937',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['935','936'])).

thf('938',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['930','937'])).

thf('939',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['938'])).

thf('940',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['925','939'])).

thf('941',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['940'])).

thf('942',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['920','941'])).

thf('943',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['942'])).

thf('944',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['890','943'])).

thf('945',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['944'])).

thf('946',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('947',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['945','946'])).

thf('948',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','947'])).

thf('949',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['948'])).

thf('950',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('951',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['949','950'])).

thf('952',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['944'])).

thf('953',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('954',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['952','953'])).

thf('955',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['951','954'])).

thf('956',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['955'])).

thf('957',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('958',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['956','957'])).

thf('959',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['949','950'])).

thf('960',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('961',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['959','960'])).

thf('962',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('963',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('964',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['961','962','963'])).

thf('965',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['964'])).

thf('966',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('967',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['965','966'])).

thf('968',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['958','967'])).

thf('969',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C )
   <= ~ ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('970',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['968','969'])).

thf('971',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('972',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('973',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('974',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['972','973'])).

thf('975',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('976',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('977',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('978',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('979',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['977','978'])).

thf('980',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('981',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['979','980'])).

thf('982',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('983',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('984',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('985',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('986',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('987',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('988',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('989',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('990',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('991',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('992',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('993',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('994',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('995',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('996',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('997',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('998',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('999',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1000',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1001',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('1002',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1003',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('1004',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1005',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('1006',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1007',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('1008',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('1009',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1007','1008'])).

thf('1010',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1011',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1007','1008'])).

thf('1012',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1013',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1011','1012'])).

thf('1014',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1015',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1013','1014'])).

thf('1016',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1010','1015'])).

thf('1017',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1016'])).

thf('1018',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1017'])).

thf('1019',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1017'])).

thf('1020',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1011','1012'])).

thf('1021',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1022',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1020','1021'])).

thf('1023',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1019','1022'])).

thf('1024',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1023'])).

thf('1025',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1026',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1024','1025'])).

thf('1027',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1028',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1029',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1026','1027','1028'])).

thf('1030',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1029'])).

thf('1031',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1018','1030'])).

thf('1032',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1031'])).

thf('1033',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1031'])).

thf('1034',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1035',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1033','1034'])).

thf('1036',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1037',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1035','1036'])).

thf('1038',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1032','1037'])).

thf('1039',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1038'])).

thf('1040',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1031'])).

thf('1041',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1033','1034'])).

thf('1042',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1043',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1041','1042'])).

thf('1044',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1040','1043'])).

thf('1045',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1044'])).

thf('1046',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1031'])).

thf('1047',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1033','1034'])).

thf('1048',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1049',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1047','1048'])).

thf('1050',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1046','1049'])).

thf('1051',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1050'])).

thf('1052',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1031'])).

thf('1053',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1033','1034'])).

thf('1054',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1055',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1053','1054'])).

thf('1056',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1052','1055'])).

thf('1057',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1056'])).

thf('1058',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1059',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1057','1058'])).

thf('1060',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1051','1059'])).

thf('1061',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1060'])).

thf('1062',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1045','1061'])).

thf('1063',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1062'])).

thf('1064',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1039','1063'])).

thf('1065',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1064'])).

thf('1066',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1009','1065'])).

thf('1067',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1066'])).

thf('1068',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1069',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1067','1068'])).

thf('1070',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1006','1069'])).

thf('1071',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1070'])).

thf('1072',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1071'])).

thf('1073',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1072'])).

thf('1074',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1072'])).

thf('1075',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1066'])).

thf('1076',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1077',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1075','1076'])).

thf('1078',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1074','1077'])).

thf('1079',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1078'])).

thf('1080',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1081',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1079','1080'])).

thf('1082',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1083',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1084',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1081','1082','1083'])).

thf('1085',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1084'])).

thf('1086',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1073','1085'])).

thf('1087',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1086'])).

thf('1088',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('1089',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1087','1088'])).

thf('1090',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1086'])).

thf('1091',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('1092',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1090','1091'])).

thf('1093',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('1094',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1092','1093'])).

thf('1095',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1089','1094'])).

thf('1096',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1095'])).

thf('1097',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('1098',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1096','1097'])).

thf('1099',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('1100',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1098','1099'])).

thf('1101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('1102',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1100','1101'])).

thf('1103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1104',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1102','1103'])).

thf('1105',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1104'])).

thf('1106',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1005','1105'])).

thf('1107',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1108',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1005','1105'])).

thf('1109',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1110',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1108','1109'])).

thf('1111',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1112',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1110','1111'])).

thf('1113',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1107','1112'])).

thf('1114',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1113'])).

thf('1115',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1114'])).

thf('1116',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1115'])).

thf('1117',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1115'])).

thf('1118',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1108','1109'])).

thf('1119',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1120',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1118','1119'])).

thf('1121',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1117','1120'])).

thf('1122',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1121'])).

thf('1123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1124',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1122','1123'])).

thf('1125',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1126',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1127',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1124','1125','1126'])).

thf('1128',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1127'])).

thf('1129',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1116','1128'])).

thf('1130',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1129'])).

thf('1131',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1129'])).

thf('1132',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1133',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1131','1132'])).

thf('1134',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1135',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1133','1134'])).

thf('1136',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1130','1135'])).

thf('1137',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1136'])).

thf('1138',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1129'])).

thf('1139',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1131','1132'])).

thf('1140',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1141',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1139','1140'])).

thf('1142',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1138','1141'])).

thf('1143',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1142'])).

thf('1144',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1129'])).

thf('1145',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1131','1132'])).

thf('1146',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1147',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1145','1146'])).

thf('1148',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1144','1147'])).

thf('1149',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1148'])).

thf('1150',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1129'])).

thf('1151',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1131','1132'])).

thf('1152',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1153',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1151','1152'])).

thf('1154',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1150','1153'])).

thf('1155',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1154'])).

thf('1156',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1157',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1155','1156'])).

thf('1158',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1149','1157'])).

thf('1159',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1158'])).

thf('1160',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1143','1159'])).

thf('1161',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1160'])).

thf('1162',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1137','1161'])).

thf('1163',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1162'])).

thf('1164',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1106','1163'])).

thf('1165',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1164'])).

thf('1166',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1167',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1165','1166'])).

thf('1168',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1004','1167'])).

thf('1169',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1168'])).

thf('1170',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1169'])).

thf('1171',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1170'])).

thf('1172',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1170'])).

thf('1173',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1164'])).

thf('1174',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1175',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1173','1174'])).

thf('1176',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1172','1175'])).

thf('1177',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1176'])).

thf('1178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1179',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1177','1178'])).

thf('1180',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1181',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1182',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1179','1180','1181'])).

thf('1183',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1182'])).

thf('1184',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1171','1183'])).

thf('1185',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1184'])).

thf('1186',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_finset_1 @ X24 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('1187',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1185','1186'])).

thf('1188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('1189',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1187','1188'])).

thf('1190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('1191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1192',plain,
    ( ! [X0: $i] :
        ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1189','1190','1191'])).

thf('1193',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1192'])).

thf('1194',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1003','1193'])).

thf('1195',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1196',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1003','1193'])).

thf('1197',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1198',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1196','1197'])).

thf('1199',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1200',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1198','1199'])).

thf('1201',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1195','1200'])).

thf('1202',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1201'])).

thf('1203',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1202'])).

thf('1204',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1203'])).

thf('1205',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1203'])).

thf('1206',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1196','1197'])).

thf('1207',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1208',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1206','1207'])).

thf('1209',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1205','1208'])).

thf('1210',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1209'])).

thf('1211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1212',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1210','1211'])).

thf('1213',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1214',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1215',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1212','1213','1214'])).

thf('1216',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1215'])).

thf('1217',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1204','1216'])).

thf('1218',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1217'])).

thf('1219',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1217'])).

thf('1220',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1221',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1219','1220'])).

thf('1222',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1223',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1221','1222'])).

thf('1224',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1218','1223'])).

thf('1225',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1224'])).

thf('1226',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1217'])).

thf('1227',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1219','1220'])).

thf('1228',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1229',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1227','1228'])).

thf('1230',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1226','1229'])).

thf('1231',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1230'])).

thf('1232',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1217'])).

thf('1233',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1219','1220'])).

thf('1234',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1235',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1233','1234'])).

thf('1236',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1232','1235'])).

thf('1237',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1236'])).

thf('1238',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1217'])).

thf('1239',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1219','1220'])).

thf('1240',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1241',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1239','1240'])).

thf('1242',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1238','1241'])).

thf('1243',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1242'])).

thf('1244',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1245',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1243','1244'])).

thf('1246',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1237','1245'])).

thf('1247',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1246'])).

thf('1248',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1231','1247'])).

thf('1249',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1248'])).

thf('1250',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1225','1249'])).

thf('1251',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1250'])).

thf('1252',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1194','1251'])).

thf('1253',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1252'])).

thf('1254',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1255',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1253','1254'])).

thf('1256',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1002','1255'])).

thf('1257',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1256'])).

thf('1258',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1257'])).

thf('1259',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1258'])).

thf('1260',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1258'])).

thf('1261',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1252'])).

thf('1262',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1263',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1261','1262'])).

thf('1264',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1260','1263'])).

thf('1265',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1264'])).

thf('1266',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1267',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1265','1266'])).

thf('1268',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1269',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1270',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1267','1268','1269'])).

thf('1271',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1270'])).

thf('1272',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1259','1271'])).

thf('1273',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1272'])).

thf('1274',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_finset_1 @ X24 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('1275',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1273','1274'])).

thf('1276',plain,
    ( ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1275'])).

thf('1277',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1278',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1276','1277'])).

thf('1279',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1184'])).

thf('1280',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('1281',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1279','1280'])).

thf('1282',plain,(
    ! [X41: $i] :
      ( ( X41 = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('1283',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1281','1282'])).

thf('1284',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1278','1283'])).

thf('1285',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1284'])).

thf('1286',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ~ ( r1_yellow_0 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('1287',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_6 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1285','1286'])).

thf('1288',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1289',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1287','1288'])).

thf('1290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('1291',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1289','1290'])).

thf('1292',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1291'])).

thf('1293',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1001','1292'])).

thf('1294',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1000','1293'])).

thf('1295',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['999','1294'])).

thf('1296',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['998','1295'])).

thf('1297',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1298',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['998','1295'])).

thf('1299',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1300',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1298','1299'])).

thf('1301',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1302',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1300','1301'])).

thf('1303',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1297','1302'])).

thf('1304',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1303'])).

thf('1305',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1304'])).

thf('1306',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1305'])).

thf('1307',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1305'])).

thf('1308',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1298','1299'])).

thf('1309',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1310',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1308','1309'])).

thf('1311',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1307','1310'])).

thf('1312',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1311'])).

thf('1313',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1314',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1312','1313'])).

thf('1315',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1316',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1317',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1314','1315','1316'])).

thf('1318',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1317'])).

thf('1319',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1306','1318'])).

thf('1320',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1319'])).

thf('1321',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1319'])).

thf('1322',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1323',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1321','1322'])).

thf('1324',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1325',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1323','1324'])).

thf('1326',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1320','1325'])).

thf('1327',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1326'])).

thf('1328',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1319'])).

thf('1329',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1321','1322'])).

thf('1330',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1331',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1329','1330'])).

thf('1332',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1328','1331'])).

thf('1333',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1332'])).

thf('1334',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1319'])).

thf('1335',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1321','1322'])).

thf('1336',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1337',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1335','1336'])).

thf('1338',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1334','1337'])).

thf('1339',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1338'])).

thf('1340',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1319'])).

thf('1341',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1321','1322'])).

thf('1342',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1343',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1341','1342'])).

thf('1344',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1340','1343'])).

thf('1345',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1344'])).

thf('1346',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1347',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1345','1346'])).

thf('1348',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1339','1347'])).

thf('1349',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1348'])).

thf('1350',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1333','1349'])).

thf('1351',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1350'])).

thf('1352',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1327','1351'])).

thf('1353',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1352'])).

thf('1354',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1296','1353'])).

thf('1355',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1354'])).

thf('1356',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1357',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1355','1356'])).

thf('1358',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['997','1357'])).

thf('1359',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1358'])).

thf('1360',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1359'])).

thf('1361',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1360'])).

thf('1362',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1360'])).

thf('1363',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1354'])).

thf('1364',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1365',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1363','1364'])).

thf('1366',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1362','1365'])).

thf('1367',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1366'])).

thf('1368',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1369',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1367','1368'])).

thf('1370',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1371',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1372',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1369','1370','1371'])).

thf('1373',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1372'])).

thf('1374',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1361','1373'])).

thf('1375',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1374'])).

thf('1376',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('1377',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1375','1376'])).

thf('1378',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1374'])).

thf('1379',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('1380',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1378','1379'])).

thf('1381',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('1382',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1380','1381'])).

thf('1383',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1382'])).

thf('1384',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1377','1383'])).

thf('1385',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1384'])).

thf('1386',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('1387',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1385','1386'])).

thf('1388',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('1389',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1387','1388'])).

thf('1390',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1291'])).

thf('1391',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1389','1390'])).

thf('1392',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1393',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1391','1392'])).

thf('1394',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1393'])).

thf('1395',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['996','1394'])).

thf('1396',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['995','1395'])).

thf('1397',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1398',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['995','1395'])).

thf('1399',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1400',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1398','1399'])).

thf('1401',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1402',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1400','1401'])).

thf('1403',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1397','1402'])).

thf('1404',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1403'])).

thf('1405',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1404'])).

thf('1406',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1405'])).

thf('1407',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1405'])).

thf('1408',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1398','1399'])).

thf('1409',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1410',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1408','1409'])).

thf('1411',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1407','1410'])).

thf('1412',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1411'])).

thf('1413',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1414',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1412','1413'])).

thf('1415',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1416',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1417',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1414','1415','1416'])).

thf('1418',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1417'])).

thf('1419',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1406','1418'])).

thf('1420',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1419'])).

thf('1421',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1419'])).

thf('1422',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1423',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1421','1422'])).

thf('1424',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1425',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1423','1424'])).

thf('1426',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1420','1425'])).

thf('1427',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1426'])).

thf('1428',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1419'])).

thf('1429',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1421','1422'])).

thf('1430',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1431',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1429','1430'])).

thf('1432',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1428','1431'])).

thf('1433',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1432'])).

thf('1434',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1419'])).

thf('1435',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1421','1422'])).

thf('1436',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1437',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1435','1436'])).

thf('1438',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1434','1437'])).

thf('1439',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1438'])).

thf('1440',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1419'])).

thf('1441',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1421','1422'])).

thf('1442',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1443',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1441','1442'])).

thf('1444',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1440','1443'])).

thf('1445',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1444'])).

thf('1446',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1447',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1445','1446'])).

thf('1448',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1439','1447'])).

thf('1449',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1448'])).

thf('1450',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1433','1449'])).

thf('1451',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1450'])).

thf('1452',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1427','1451'])).

thf('1453',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1452'])).

thf('1454',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1396','1453'])).

thf('1455',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1454'])).

thf('1456',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1457',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1455','1456'])).

thf('1458',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['994','1457'])).

thf('1459',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1458'])).

thf('1460',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1459'])).

thf('1461',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1460'])).

thf('1462',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1460'])).

thf('1463',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1454'])).

thf('1464',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1465',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1463','1464'])).

thf('1466',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1462','1465'])).

thf('1467',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1466'])).

thf('1468',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1469',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1467','1468'])).

thf('1470',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1471',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1472',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1469','1470','1471'])).

thf('1473',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1472'])).

thf('1474',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1461','1473'])).

thf('1475',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1474'])).

thf('1476',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1276','1277'])).

thf('1477',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1478',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['981','982'])).

thf('1479',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1474'])).

thf('1480',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('1481',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1479','1480'])).

thf('1482',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('1483',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1484',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1481','1482','1483'])).

thf('1485',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1484'])).

thf('1486',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1478','1485'])).

thf('1487',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1488',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1478','1485'])).

thf('1489',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1490',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1488','1489'])).

thf('1491',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1492',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1490','1491'])).

thf('1493',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1487','1492'])).

thf('1494',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1493'])).

thf('1495',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1494'])).

thf('1496',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1495'])).

thf('1497',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1495'])).

thf('1498',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1488','1489'])).

thf('1499',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1500',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1498','1499'])).

thf('1501',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1497','1500'])).

thf('1502',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1501'])).

thf('1503',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1504',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1502','1503'])).

thf('1505',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1506',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1507',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1504','1505','1506'])).

thf('1508',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1507'])).

thf('1509',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1496','1508'])).

thf('1510',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1509'])).

thf('1511',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1509'])).

thf('1512',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1513',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1511','1512'])).

thf('1514',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1515',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1513','1514'])).

thf('1516',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1510','1515'])).

thf('1517',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1516'])).

thf('1518',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1509'])).

thf('1519',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1511','1512'])).

thf('1520',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1521',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1519','1520'])).

thf('1522',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1518','1521'])).

thf('1523',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1522'])).

thf('1524',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1509'])).

thf('1525',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1511','1512'])).

thf('1526',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1527',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1525','1526'])).

thf('1528',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1524','1527'])).

thf('1529',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1528'])).

thf('1530',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1509'])).

thf('1531',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1511','1512'])).

thf('1532',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1533',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1531','1532'])).

thf('1534',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1530','1533'])).

thf('1535',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1534'])).

thf('1536',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1537',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1535','1536'])).

thf('1538',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1529','1537'])).

thf('1539',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1538'])).

thf('1540',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1523','1539'])).

thf('1541',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1540'])).

thf('1542',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1517','1541'])).

thf('1543',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1542'])).

thf('1544',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1486','1543'])).

thf('1545',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1544'])).

thf('1546',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1547',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1545','1546'])).

thf('1548',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1477','1547'])).

thf('1549',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1548'])).

thf('1550',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1549'])).

thf('1551',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1550'])).

thf('1552',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1550'])).

thf('1553',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1544'])).

thf('1554',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1555',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1553','1554'])).

thf('1556',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1552','1555'])).

thf('1557',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1556'])).

thf('1558',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1559',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1557','1558'])).

thf('1560',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1561',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1562',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1559','1560','1561'])).

thf('1563',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1562'])).

thf('1564',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1551','1563'])).

thf('1565',plain,
    ( ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1564'])).

thf('1566',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('1567',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1565','1566'])).

thf('1568',plain,(
    ! [X41: $i] :
      ( ( X41 = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('1569',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1567','1568'])).

thf('1570',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1569'])).

thf('1571',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1476','1570'])).

thf('1572',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1571'])).

thf('1573',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ~ ( r1_yellow_0 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('1574',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_6 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1572','1573'])).

thf('1575',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1576',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1574','1575'])).

thf('1577',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('1578',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1576','1577'])).

thf('1579',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1578'])).

thf('1580',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1475','1579'])).

thf('1581',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('1582',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1583',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1580','1581','1582'])).

thf('1584',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1583'])).

thf('1585',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['993','1584'])).

thf('1586',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['992','1585'])).

thf('1587',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1588',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['992','1585'])).

thf('1589',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1590',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1588','1589'])).

thf('1591',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1592',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1590','1591'])).

thf('1593',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1587','1592'])).

thf('1594',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1593'])).

thf('1595',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1594'])).

thf('1596',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1595'])).

thf('1597',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1595'])).

thf('1598',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1588','1589'])).

thf('1599',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1600',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1598','1599'])).

thf('1601',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1597','1600'])).

thf('1602',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1601'])).

thf('1603',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1604',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1602','1603'])).

thf('1605',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1606',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1607',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1604','1605','1606'])).

thf('1608',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1607'])).

thf('1609',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1596','1608'])).

thf('1610',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1609'])).

thf('1611',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1609'])).

thf('1612',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1613',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1611','1612'])).

thf('1614',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1615',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1613','1614'])).

thf('1616',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1610','1615'])).

thf('1617',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1616'])).

thf('1618',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1609'])).

thf('1619',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1611','1612'])).

thf('1620',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1621',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1619','1620'])).

thf('1622',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1618','1621'])).

thf('1623',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1622'])).

thf('1624',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1609'])).

thf('1625',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1611','1612'])).

thf('1626',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1627',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1625','1626'])).

thf('1628',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1624','1627'])).

thf('1629',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1628'])).

thf('1630',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1609'])).

thf('1631',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1611','1612'])).

thf('1632',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1633',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1631','1632'])).

thf('1634',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1630','1633'])).

thf('1635',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1634'])).

thf('1636',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1637',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1635','1636'])).

thf('1638',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1629','1637'])).

thf('1639',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1638'])).

thf('1640',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1623','1639'])).

thf('1641',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1640'])).

thf('1642',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1617','1641'])).

thf('1643',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1642'])).

thf('1644',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1586','1643'])).

thf('1645',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1644'])).

thf('1646',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1647',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1645','1646'])).

thf('1648',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['991','1647'])).

thf('1649',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1648'])).

thf('1650',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1649'])).

thf('1651',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1650'])).

thf('1652',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1650'])).

thf('1653',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1644'])).

thf('1654',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1655',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_3 @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1653','1654'])).

thf('1656',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1652','1655'])).

thf('1657',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1656'])).

thf('1658',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1659',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1657','1658'])).

thf('1660',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1661',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1662',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1659','1660','1661'])).

thf('1663',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1662'])).

thf('1664',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1651','1663'])).

thf('1665',plain,
    ( ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1664'])).

thf('1666',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1667',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1665','1666'])).

thf('1668',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('1669',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_7 @ o_0_0_xboole_0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1667','1668'])).

thf('1670',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_7 @ o_0_0_xboole_0 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['703','704'])).

thf('1671',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1669','1670'])).

thf('1672',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['990','1671'])).

thf('1673',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['989','1672'])).

thf('1674',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['988','1673'])).

thf('1675',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['987','1674'])).

thf('1676',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1677',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['987','1674'])).

thf('1678',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1679',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1677','1678'])).

thf('1680',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1681',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1679','1680'])).

thf('1682',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1676','1681'])).

thf('1683',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1682'])).

thf('1684',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1683'])).

thf('1685',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1684'])).

thf('1686',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1684'])).

thf('1687',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1677','1678'])).

thf('1688',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1689',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1687','1688'])).

thf('1690',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1686','1689'])).

thf('1691',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1690'])).

thf('1692',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1693',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1691','1692'])).

thf('1694',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1695',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1696',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1693','1694','1695'])).

thf('1697',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1696'])).

thf('1698',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1685','1697'])).

thf('1699',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1698'])).

thf('1700',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1698'])).

thf('1701',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1702',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1700','1701'])).

thf('1703',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1704',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1702','1703'])).

thf('1705',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1699','1704'])).

thf('1706',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1705'])).

thf('1707',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1698'])).

thf('1708',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1700','1701'])).

thf('1709',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1710',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1708','1709'])).

thf('1711',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1707','1710'])).

thf('1712',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1711'])).

thf('1713',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1698'])).

thf('1714',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1700','1701'])).

thf('1715',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1716',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1714','1715'])).

thf('1717',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1713','1716'])).

thf('1718',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1717'])).

thf('1719',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1698'])).

thf('1720',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1700','1701'])).

thf('1721',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1722',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1720','1721'])).

thf('1723',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1719','1722'])).

thf('1724',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1723'])).

thf('1725',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1726',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1724','1725'])).

thf('1727',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1718','1726'])).

thf('1728',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1727'])).

thf('1729',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1712','1728'])).

thf('1730',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1729'])).

thf('1731',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1706','1730'])).

thf('1732',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1731'])).

thf('1733',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1675','1732'])).

thf('1734',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1733'])).

thf('1735',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1736',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1734','1735'])).

thf('1737',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['986','1736'])).

thf('1738',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1737'])).

thf('1739',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1738'])).

thf('1740',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1739'])).

thf('1741',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1739'])).

thf('1742',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1733'])).

thf('1743',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1744',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1742','1743'])).

thf('1745',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1741','1744'])).

thf('1746',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1745'])).

thf('1747',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1748',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1746','1747'])).

thf('1749',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1750',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1751',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1748','1749','1750'])).

thf('1752',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1751'])).

thf('1753',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1740','1752'])).

thf('1754',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1753'])).

thf('1755',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1756',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1754','1755'])).

thf('1757',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('1758',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1756','1757'])).

thf('1759',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1754','1755'])).

thf('1760',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('1761',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1759','1760'])).

thf('1762',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('1763',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1761','1762'])).

thf('1764',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1758','1763'])).

thf('1765',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1764'])).

thf('1766',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('1767',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1765','1766'])).

thf('1768',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('1769',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1767','1768'])).

thf('1770',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['990','1671'])).

thf('1771',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1769','1770'])).

thf('1772',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1773',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1771','1772'])).

thf('1774',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1773'])).

thf('1775',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['985','1774'])).

thf('1776',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1777',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['985','1774'])).

thf('1778',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1779',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1777','1778'])).

thf('1780',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1781',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1779','1780'])).

thf('1782',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1776','1781'])).

thf('1783',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1782'])).

thf('1784',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1783'])).

thf('1785',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1784'])).

thf('1786',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1784'])).

thf('1787',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1777','1778'])).

thf('1788',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1789',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1787','1788'])).

thf('1790',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1786','1789'])).

thf('1791',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1790'])).

thf('1792',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1793',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1791','1792'])).

thf('1794',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1795',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1796',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1793','1794','1795'])).

thf('1797',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1796'])).

thf('1798',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1785','1797'])).

thf('1799',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1798'])).

thf('1800',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1798'])).

thf('1801',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1802',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1800','1801'])).

thf('1803',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1804',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1802','1803'])).

thf('1805',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1799','1804'])).

thf('1806',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1805'])).

thf('1807',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1798'])).

thf('1808',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1800','1801'])).

thf('1809',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1810',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1808','1809'])).

thf('1811',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1807','1810'])).

thf('1812',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1811'])).

thf('1813',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1798'])).

thf('1814',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1800','1801'])).

thf('1815',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1816',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1814','1815'])).

thf('1817',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1813','1816'])).

thf('1818',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1817'])).

thf('1819',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1798'])).

thf('1820',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1800','1801'])).

thf('1821',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1822',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1820','1821'])).

thf('1823',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1819','1822'])).

thf('1824',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1823'])).

thf('1825',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1826',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1824','1825'])).

thf('1827',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1818','1826'])).

thf('1828',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1827'])).

thf('1829',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1812','1828'])).

thf('1830',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1829'])).

thf('1831',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1806','1830'])).

thf('1832',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1831'])).

thf('1833',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1775','1832'])).

thf('1834',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1833'])).

thf('1835',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1836',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1834','1835'])).

thf('1837',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['984','1836'])).

thf('1838',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1837'])).

thf('1839',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1838'])).

thf('1840',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1839'])).

thf('1841',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1839'])).

thf('1842',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1833'])).

thf('1843',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1844',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
          = o_0_0_xboole_0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1842','1843'])).

thf('1845',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1841','1844'])).

thf('1846',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1845'])).

thf('1847',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1848',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1846','1847'])).

thf('1849',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1850',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1851',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1848','1849','1850'])).

thf('1852',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1851'])).

thf('1853',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1840','1852'])).

thf('1854',plain,
    ( ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1853'])).

thf('1855',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1856',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1854','1855'])).

thf('1857',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['990','1671'])).

thf('1858',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1856','1857'])).

thf('1859',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('1860',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1861',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1858','1859','1860'])).

thf('1862',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1861'])).

thf('1863',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['983','1862'])).

thf('1864',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['974','975'])).

thf('1865',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['983','1862'])).

thf('1866',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('1867',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1865','1866'])).

thf('1868',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1869',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1867','1868'])).

thf('1870',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1864','1869'])).

thf('1871',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1870'])).

thf('1872',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1871'])).

thf('1873',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1872'])).

thf('1874',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1872'])).

thf('1875',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1865','1866'])).

thf('1876',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1877',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1875','1876'])).

thf('1878',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1874','1877'])).

thf('1879',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1878'])).

thf('1880',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1881',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1879','1880'])).

thf('1882',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1883',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1884',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1881','1882','1883'])).

thf('1885',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1884'])).

thf('1886',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1873','1885'])).

thf('1887',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1886'])).

thf('1888',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1889',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1887','1888'])).

thf('1890',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('1891',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1889','1890'])).

thf('1892',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1893',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1891','1892'])).

thf('1894',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1887','1888'])).

thf('1895',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1893','1894'])).

thf('1896',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1889','1890'])).

thf('1897',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1898',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1896','1897'])).

thf('1899',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1887','1888'])).

thf('1900',plain,
    ( ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1898','1899'])).

thf('1901',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1889','1890'])).

thf('1902',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1903',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1901','1902'])).

thf('1904',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1887','1888'])).

thf('1905',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1903','1904'])).

thf('1906',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1889','1890'])).

thf('1907',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1908',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1906','1907'])).

thf('1909',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1887','1888'])).

thf('1910',plain,
    ( ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1908','1909'])).

thf('1911',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('1912',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1910','1911'])).

thf('1913',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1905','1912'])).

thf('1914',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1913'])).

thf('1915',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1900','1914'])).

thf('1916',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1915'])).

thf('1917',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1895','1916'])).

thf('1918',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1917'])).

thf('1919',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1863','1918'])).

thf('1920',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1919'])).

thf('1921',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1922',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1920','1921'])).

thf('1923',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['976','1922'])).

thf('1924',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ X0 ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1923'])).

thf('1925',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(eq_fact,[status(thm)],['1924'])).

thf('1926',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1925'])).

thf('1927',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1928',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1926','1927'])).

thf('1929',plain,
    ( ! [X0: $i] :
        ( ( r1_yellow_0 @ sk_A @ X0 )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ sk_C @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1919'])).

thf('1930',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1931',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1929','1930'])).

thf('1932',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1928','1931'])).

thf('1933',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1932'])).

thf('1934',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1935',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1933','1934'])).

thf('1936',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_0])).

thf('1937',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1935','1936'])).

thf('1938',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1939',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_C )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('1940',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['1937','1938','1939'])).

thf('1941',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['1940'])).

thf('1942',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1926','1927'])).

thf('1943',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1941','1942'])).

thf('1944',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1945',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['1943','1944'])).

thf('1946',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_B )
   <= ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('1947',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_C )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1945','1946'])).

thf('1948',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','970','971','1947'])).


%------------------------------------------------------------------------------
