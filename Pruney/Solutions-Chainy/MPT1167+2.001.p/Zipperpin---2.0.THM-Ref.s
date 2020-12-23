%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6yzCF1agpt

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:07 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 872 expanded)
%              Number of leaves         :   25 ( 256 expanded)
%              Depth                    :   29
%              Number of atoms          : 1393 (24317 expanded)
%              Number of equality atoms :   59 ( 267 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t70_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( ( r2_orders_2 @ A @ B @ C )
                          & ( r2_hidden @ B @ D )
                          & ( r2_hidden @ C @ E )
                          & ( m1_orders_2 @ E @ A @ D ) )
                       => ( r2_hidden @ B @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( ( r2_orders_2 @ A @ B @ C )
                            & ( r2_hidden @ B @ D )
                            & ( r2_hidden @ C @ E )
                            & ( m1_orders_2 @ E @ A @ D ) )
                         => ( r2_hidden @ B @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_orders_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d15_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( B != k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ? [D: $i] :
                        ( ( C
                          = ( k3_orders_2 @ A @ B @ D ) )
                        & ( r2_hidden @ D @ B )
                        & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) )
                & ( ( B = k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ( C = k1_xboole_0 ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( X5
        = ( k3_orders_2 @ X4 @ X3 @ ( sk_D @ X5 @ X3 @ X4 ) ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) ) )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) ) )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k3_orders_2 @ X12 @ X13 @ X14 ) )
      | ( r2_orders_2 @ X12 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['17','43'])).

thf('45',plain,(
    r2_hidden @ sk_C @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( ( r2_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ C @ D ) )
                      | ( ( r1_orders_2 @ A @ B @ C )
                        & ( r2_orders_2 @ A @ C @ D ) ) )
                   => ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r2_orders_2 @ X8 @ X10 @ X9 )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t32_orders_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','68'])).

thf('70',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','69'])).

thf('71',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('73',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_orders_2 @ X12 @ X11 @ X14 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ( r2_hidden @ X11 @ ( k3_orders_2 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','88'])).

thf('90',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_E ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','92'])).

thf('94',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('95',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','101'])).

thf('103',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['90','91'])).

thf('105',plain,(
    m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_E = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_E = k1_xboole_0 ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['90','91'])).

thf('111',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6yzCF1agpt
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 139 iterations in 0.089s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.35/0.57  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.35/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.57  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.35/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.57  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.35/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.57  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.35/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.57  thf(t70_orders_2, conjecture,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57               ( ![D:$i]:
% 0.35/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57                   ( ![E:$i]:
% 0.35/0.57                     ( ( m1_subset_1 @
% 0.35/0.57                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.35/0.57                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 0.35/0.57                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 0.35/0.57                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.57    (~( ![A:$i]:
% 0.35/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57          ( ![B:$i]:
% 0.35/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57              ( ![C:$i]:
% 0.35/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57                  ( ![D:$i]:
% 0.35/0.57                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57                      ( ![E:$i]:
% 0.35/0.57                        ( ( m1_subset_1 @
% 0.35/0.57                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57                          ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.35/0.57                              ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 0.35/0.57                              ( m1_orders_2 @ E @ A @ D ) ) =>
% 0.35/0.57                            ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t70_orders_2])).
% 0.35/0.57  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(d15_orders_2, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.57                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.35/0.57                     ( ?[D:$i]:
% 0.35/0.57                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.35/0.57                         ( r2_hidden @ D @ B ) & 
% 0.35/0.57                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.35/0.57                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.35/0.57                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ((X3) = (k1_xboole_0))
% 0.35/0.57          | ((X5) = (k3_orders_2 @ X4 @ X3 @ (sk_D @ X5 @ X3 @ X4)))
% 0.35/0.57          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ~ (l1_orders_2 @ X4)
% 0.35/0.57          | ~ (v5_orders_2 @ X4)
% 0.35/0.57          | ~ (v4_orders_2 @ X4)
% 0.35/0.57          | ~ (v3_orders_2 @ X4)
% 0.35/0.57          | (v2_struct_0 @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.57          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.35/0.57          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.57  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.57          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.35/0.57          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | ((sk_E)
% 0.35/0.57            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['3', '11'])).
% 0.35/0.57  thf('13', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('14', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | ((sk_E)
% 0.35/0.57            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.35/0.57  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('clc', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('17', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('20', plain,
% 0.35/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ((X3) = (k1_xboole_0))
% 0.35/0.57          | (m1_subset_1 @ (sk_D @ X5 @ X3 @ X4) @ (u1_struct_0 @ X4))
% 0.35/0.57          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ~ (l1_orders_2 @ X4)
% 0.35/0.57          | ~ (v5_orders_2 @ X4)
% 0.35/0.57          | ~ (v4_orders_2 @ X4)
% 0.35/0.57          | ~ (v3_orders_2 @ X4)
% 0.35/0.57          | (v2_struct_0 @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.35/0.57  thf('21', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.57          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.35/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.57  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('26', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.57          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.35/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.35/0.57  thf('27', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['18', '26'])).
% 0.35/0.57  thf('28', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('29', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.35/0.57  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('31', plain,
% 0.35/0.57      (((m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.57  thf('32', plain,
% 0.35/0.57      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('clc', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('33', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(t57_orders_2, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57               ( ![D:$i]:
% 0.35/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.35/0.57                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf('34', plain,
% 0.35/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.35/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.35/0.57          | ~ (r2_hidden @ X11 @ (k3_orders_2 @ X12 @ X13 @ X14))
% 0.35/0.57          | (r2_orders_2 @ X12 @ X11 @ X14)
% 0.35/0.57          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.35/0.57          | ~ (l1_orders_2 @ X12)
% 0.35/0.57          | ~ (v5_orders_2 @ X12)
% 0.35/0.57          | ~ (v4_orders_2 @ X12)
% 0.35/0.57          | ~ (v3_orders_2 @ X12)
% 0.35/0.57          | (v2_struct_0 @ X12))),
% 0.35/0.57      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.35/0.57  thf('35', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.35/0.57          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.57  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('40', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.35/0.57          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.35/0.57  thf('41', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X0 @ sk_E)
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['32', '40'])).
% 0.35/0.57  thf('42', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((sk_D_1) = (k1_xboole_0))
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0))
% 0.35/0.57          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.35/0.57      inference('sup-', [status(thm)], ['31', '41'])).
% 0.35/0.57  thf('43', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X0 @ sk_E)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.35/0.57  thf('44', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57        | ~ (r2_hidden @ sk_C @ sk_E))),
% 0.35/0.57      inference('sup-', [status(thm)], ['17', '43'])).
% 0.35/0.57  thf('45', plain, ((r2_hidden @ sk_C @ sk_E)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('46', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.35/0.57  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('48', plain,
% 0.35/0.57      (((r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('clc', [status(thm)], ['46', '47'])).
% 0.35/0.57  thf('49', plain,
% 0.35/0.57      (((m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.57  thf('50', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(t32_orders_2, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57               ( ![D:$i]:
% 0.35/0.57                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.35/0.57                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.35/0.57                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.35/0.57                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.35/0.57                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf('52', plain,
% 0.35/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.35/0.57          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.35/0.57          | (r2_orders_2 @ X8 @ X7 @ X9)
% 0.35/0.57          | ~ (r2_orders_2 @ X8 @ X10 @ X9)
% 0.35/0.57          | ~ (r1_orders_2 @ X8 @ X7 @ X10)
% 0.35/0.57          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.35/0.57          | ~ (l1_orders_2 @ X8)
% 0.35/0.57          | ~ (v5_orders_2 @ X8)
% 0.35/0.57          | ~ (v4_orders_2 @ X8))),
% 0.35/0.57      inference('cnf', [status(esa)], [t32_orders_2])).
% 0.35/0.57  thf('53', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.35/0.57          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.57  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('57', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.35/0.57          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.35/0.57  thf('58', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.35/0.57          | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.35/0.57      inference('sup-', [status(thm)], ['50', '57'])).
% 0.35/0.57  thf('59', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('60', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(d10_orders_2, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( l1_orders_2 @ A ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.35/0.57                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf('61', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.35/0.57          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.35/0.57          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.35/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.35/0.57          | ~ (l1_orders_2 @ X1))),
% 0.35/0.57      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.35/0.57  thf('62', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.35/0.57  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('64', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.35/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.35/0.57  thf('65', plain,
% 0.35/0.57      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.35/0.57        | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.35/0.57      inference('sup-', [status(thm)], ['59', '64'])).
% 0.35/0.57  thf('66', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('67', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.35/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.35/0.57  thf('68', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.35/0.57      inference('demod', [status(thm)], ['58', '67'])).
% 0.35/0.57  thf('69', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | ~ (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57        | (r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['49', '68'])).
% 0.35/0.57  thf('70', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['48', '69'])).
% 0.35/0.57  thf('71', plain,
% 0.35/0.57      (((r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['70'])).
% 0.35/0.57  thf('72', plain,
% 0.35/0.57      (((m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.57  thf('73', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('74', plain,
% 0.35/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.35/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.35/0.57          | ~ (r2_orders_2 @ X12 @ X11 @ X14)
% 0.35/0.57          | ~ (r2_hidden @ X11 @ X13)
% 0.35/0.57          | (r2_hidden @ X11 @ (k3_orders_2 @ X12 @ X13 @ X14))
% 0.35/0.57          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.35/0.57          | ~ (l1_orders_2 @ X12)
% 0.35/0.57          | ~ (v5_orders_2 @ X12)
% 0.35/0.57          | ~ (v4_orders_2 @ X12)
% 0.35/0.57          | ~ (v3_orders_2 @ X12)
% 0.35/0.57          | (v2_struct_0 @ X12))),
% 0.35/0.57      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.35/0.57  thf('75', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.35/0.57          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.35/0.57  thf('76', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('77', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('78', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('80', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.35/0.57          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.35/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.35/0.57  thf('81', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((sk_D_1) = (k1_xboole_0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.35/0.57          | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.35/0.57          | (r2_hidden @ X0 @ 
% 0.35/0.57             (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['72', '80'])).
% 0.35/0.57  thf('82', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_hidden @ sk_B @ 
% 0.35/0.57           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | ~ (r2_hidden @ sk_B @ sk_D_1)
% 0.35/0.57        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['71', '81'])).
% 0.35/0.57  thf('83', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('85', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_hidden @ sk_B @ 
% 0.35/0.57           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.35/0.57  thf('86', plain,
% 0.35/0.57      (((r2_hidden @ sk_B @ 
% 0.35/0.57         (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['85'])).
% 0.35/0.57  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('88', plain,
% 0.35/0.57      ((((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | (r2_hidden @ sk_B @ 
% 0.35/0.57           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))))),
% 0.35/0.57      inference('clc', [status(thm)], ['86', '87'])).
% 0.35/0.57  thf('89', plain,
% 0.35/0.57      (((r2_hidden @ sk_B @ sk_E)
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0))
% 0.35/0.57        | ((sk_D_1) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup+', [status(thm)], ['16', '88'])).
% 0.35/0.57  thf('90', plain, ((((sk_D_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_E))),
% 0.35/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.35/0.57  thf('91', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('92', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.35/0.57      inference('clc', [status(thm)], ['90', '91'])).
% 0.35/0.57  thf('93', plain,
% 0.35/0.57      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['2', '92'])).
% 0.35/0.57  thf('94', plain,
% 0.35/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ((X3) != (k1_xboole_0))
% 0.35/0.57          | ((X5) = (k1_xboole_0))
% 0.35/0.57          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ~ (l1_orders_2 @ X4)
% 0.35/0.57          | ~ (v5_orders_2 @ X4)
% 0.35/0.57          | ~ (v4_orders_2 @ X4)
% 0.35/0.57          | ~ (v3_orders_2 @ X4)
% 0.35/0.57          | (v2_struct_0 @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.35/0.57  thf('95', plain,
% 0.35/0.57      (![X4 : $i, X5 : $i]:
% 0.35/0.57         ((v2_struct_0 @ X4)
% 0.35/0.57          | ~ (v3_orders_2 @ X4)
% 0.35/0.57          | ~ (v4_orders_2 @ X4)
% 0.35/0.57          | ~ (v5_orders_2 @ X4)
% 0.35/0.57          | ~ (l1_orders_2 @ X4)
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.57          | ~ (m1_orders_2 @ X5 @ X4 @ k1_xboole_0)
% 0.35/0.57          | ((X5) = (k1_xboole_0))
% 0.35/0.57          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.35/0.57      inference('simplify', [status(thm)], ['94'])).
% 0.35/0.57  thf('96', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((X0) = (k1_xboole_0))
% 0.35/0.57          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['93', '95'])).
% 0.35/0.57  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('98', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('99', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('100', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('101', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((X0) = (k1_xboole_0))
% 0.35/0.57          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.35/0.57  thf('102', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | ~ (m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0)
% 0.35/0.57        | ((sk_E) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['1', '101'])).
% 0.35/0.57  thf('103', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('104', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.35/0.57      inference('clc', [status(thm)], ['90', '91'])).
% 0.35/0.57  thf('105', plain, ((m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0)),
% 0.35/0.57      inference('demod', [status(thm)], ['103', '104'])).
% 0.35/0.57  thf('106', plain, (((v2_struct_0 @ sk_A) | ((sk_E) = (k1_xboole_0)))),
% 0.35/0.57      inference('demod', [status(thm)], ['102', '105'])).
% 0.35/0.57  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('108', plain, (((sk_E) = (k1_xboole_0))),
% 0.35/0.57      inference('clc', [status(thm)], ['106', '107'])).
% 0.35/0.57  thf('109', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('110', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.35/0.57      inference('clc', [status(thm)], ['90', '91'])).
% 0.35/0.57  thf('111', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.35/0.57      inference('demod', [status(thm)], ['109', '110'])).
% 0.35/0.57  thf('112', plain, ($false),
% 0.35/0.57      inference('demod', [status(thm)], ['0', '108', '111'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
