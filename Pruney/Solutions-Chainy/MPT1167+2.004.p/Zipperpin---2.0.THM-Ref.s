%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xfR6GP7XhM

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 826 expanded)
%              Number of leaves         :   23 ( 243 expanded)
%              Depth                    :   29
%              Number of atoms          : 1298 (23222 expanded)
%              Number of equality atoms :   58 ( 264 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X2
        = ( k3_orders_2 @ X1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X8 @ ( k3_orders_2 @ X9 @ X10 @ X11 ) )
      | ( r2_orders_2 @ X9 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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

thf(t29_orders_2,axiom,(
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
                 => ( ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_orders_2 @ A @ C @ D ) )
                   => ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r2_orders_2 @ X5 @ X7 @ X6 )
      | ~ ( r2_orders_2 @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t29_orders_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
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
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('65',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_orders_2 @ X9 @ X8 @ X11 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ X8 @ ( k3_orders_2 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('67',plain,(
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','80'])).

thf('82',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_E ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('87',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_orders_2 @ X2 @ X1 @ k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','93'])).

thf('95',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['82','83'])).

thf('97',plain,(
    m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_E = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_E = k1_xboole_0 ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['82','83'])).

thf('103',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','100','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xfR6GP7XhM
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 97 iterations in 0.072s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.21/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.53  thf(t70_orders_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @
% 0.21/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.53                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 0.21/0.53                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 0.21/0.53                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @
% 0.21/0.53                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                          ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.53                              ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 0.21/0.53                              ( m1_orders_2 @ E @ A @ D ) ) =>
% 0.21/0.53                            ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t70_orders_2])).
% 0.21/0.53  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d15_orders_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.21/0.53                     ( ?[D:$i]:
% 0.21/0.53                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.21/0.53                         ( r2_hidden @ D @ B ) & 
% 0.21/0.53                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.21/0.53                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.21/0.53                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ((X0) = (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k3_orders_2 @ X1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 0.21/0.53          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ~ (l1_orders_2 @ X1)
% 0.21/0.53          | ~ (v5_orders_2 @ X1)
% 0.21/0.53          | ~ (v4_orders_2 @ X1)
% 0.21/0.53          | ~ (v3_orders_2 @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.21/0.53          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.21/0.53          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | ((sk_E)
% 0.21/0.53            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '11'])).
% 0.21/0.53  thf('13', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | ((sk_E)
% 0.21/0.53            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ((X0) = (k1_xboole_0))
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ~ (l1_orders_2 @ X1)
% 0.21/0.53          | ~ (v5_orders_2 @ X1)
% 0.21/0.53          | ~ (v4_orders_2 @ X1)
% 0.21/0.53          | ~ (v3_orders_2 @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '26'])).
% 0.21/0.53  thf('28', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t57_orders_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.21/0.53                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.21/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | ~ (r2_hidden @ X8 @ (k3_orders_2 @ X9 @ X10 @ X11))
% 0.21/0.53          | (r2_orders_2 @ X9 @ X8 @ X11)
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.21/0.53          | ~ (l1_orders_2 @ X9)
% 0.21/0.53          | ~ (v5_orders_2 @ X9)
% 0.21/0.53          | ~ (v4_orders_2 @ X9)
% 0.21/0.53          | ~ (v3_orders_2 @ X9)
% 0.21/0.53          | (v2_struct_0 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_E)
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53          | ~ (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ 
% 0.21/0.53               (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_D_1) = (k1_xboole_0))
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_E)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53        | ~ (r2_hidden @ sk_C @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '43'])).
% 0.21/0.53  thf('45', plain, ((r2_hidden @ sk_C @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('50', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t29_orders_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                   ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.53                       ( r2_orders_2 @ A @ C @ D ) ) =>
% 0.21/0.53                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.53          | (r2_orders_2 @ X5 @ X4 @ X6)
% 0.21/0.53          | ~ (r2_orders_2 @ X5 @ X7 @ X6)
% 0.21/0.53          | ~ (r2_orders_2 @ X5 @ X4 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.21/0.53          | ~ (l1_orders_2 @ X5)
% 0.21/0.53          | ~ (v5_orders_2 @ X5)
% 0.21/0.53          | ~ (v4_orders_2 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t29_orders_2])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.53          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.53          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '57'])).
% 0.21/0.53  thf('59', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | ~ (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53        | (r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '60'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (((r2_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.21/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | ~ (r2_orders_2 @ X9 @ X8 @ X11)
% 0.21/0.53          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.53          | (r2_hidden @ X8 @ (k3_orders_2 @ X9 @ X10 @ X11))
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.21/0.53          | ~ (l1_orders_2 @ X9)
% 0.21/0.53          | ~ (v5_orders_2 @ X9)
% 0.21/0.53          | ~ (v4_orders_2 @ X9)
% 0.21/0.53          | ~ (v3_orders_2 @ X9)
% 0.21/0.53          | (v2_struct_0 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.21/0.53          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.53  thf('68', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.21/0.53          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_D_1) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.21/0.53          | (r2_hidden @ X0 @ 
% 0.21/0.53             (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['64', '72'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r2_hidden @ sk_B @ 
% 0.21/0.53           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ sk_D_1)
% 0.21/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '73'])).
% 0.21/0.53  thf('75', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('76', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r2_hidden @ sk_B @ 
% 0.21/0.53           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ 
% 0.21/0.53         (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['77'])).
% 0.21/0.53  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | (r2_hidden @ sk_B @ 
% 0.21/0.53           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ sk_E)
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0))
% 0.21/0.53        | ((sk_D_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['16', '80'])).
% 0.21/0.53  thf('82', plain, ((((sk_D_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_E))),
% 0.21/0.53      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.53  thf('83', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.21/0.53      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '84'])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ((X0) != (k1_xboole_0))
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ~ (l1_orders_2 @ X1)
% 0.21/0.53          | ~ (v5_orders_2 @ X1)
% 0.21/0.53          | ~ (v4_orders_2 @ X1)
% 0.21/0.53          | ~ (v3_orders_2 @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X1)
% 0.21/0.53          | ~ (v3_orders_2 @ X1)
% 0.21/0.53          | ~ (v4_orders_2 @ X1)
% 0.21/0.53          | ~ (v5_orders_2 @ X1)
% 0.21/0.53          | ~ (l1_orders_2 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.53          | ~ (m1_orders_2 @ X2 @ X1 @ k1_xboole_0)
% 0.21/0.53          | ((X2) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['85', '87'])).
% 0.21/0.53  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('91', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0)
% 0.21/0.53        | ((sk_E) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '93'])).
% 0.21/0.53  thf('95', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('96', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.21/0.53      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.53  thf('97', plain, ((m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['95', '96'])).
% 0.21/0.53  thf('98', plain, (((v2_struct_0 @ sk_A) | ((sk_E) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['94', '97'])).
% 0.21/0.54  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('100', plain, (((sk_E) = (k1_xboole_0))),
% 0.21/0.54      inference('clc', [status(thm)], ['98', '99'])).
% 0.21/0.54  thf('101', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('102', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.21/0.54      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.54  thf('103', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.54  thf('104', plain, ($false),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '100', '103'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
