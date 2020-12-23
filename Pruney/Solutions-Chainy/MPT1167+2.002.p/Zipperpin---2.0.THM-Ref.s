%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OpEssXmNXa

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:07 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 279 expanded)
%              Number of leaves         :   28 (  93 expanded)
%              Depth                    :   23
%              Number of atoms          : 1256 (7160 expanded)
%              Number of equality atoms :   46 (  74 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10 = k1_xboole_0 )
      | ( X12
        = ( k3_orders_2 @ X11 @ X10 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ~ ( m1_orders_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_orders_2 @ X15 @ X14 @ X17 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ( r2_hidden @ X14 @ ( k3_orders_2 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('21',plain,(
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
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( m1_orders_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) @ sk_D_1 )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) @ sk_D_1 )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ sk_D_1 )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k3_orders_2 @ X15 @ X16 @ X17 ) )
      | ( r2_orders_2 @ X15 @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('56',plain,(
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
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['34','64'])).

thf('66',plain,(
    r2_hidden @ sk_C_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_orders_2,axiom,(
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
                 => ( ( r2_orders_2 @ A @ B @ C )
                   => ( r1_tarski @ ( k3_orders_2 @ A @ D @ B ) @ ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k3_orders_2 @ X19 @ X20 @ X18 ) @ ( k3_orders_2 @ X19 @ X20 @ X21 ) )
      | ~ ( r2_orders_2 @ X19 @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_orders_2])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X1 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X1 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','87'])).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('93',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['2','92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OpEssXmNXa
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 181 iterations in 0.151s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.63  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.37/0.63  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.63  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.37/0.63  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.37/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.63  thf(t70_orders_2, conjecture,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63               ( ![D:$i]:
% 0.37/0.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63                   ( ![E:$i]:
% 0.37/0.63                     ( ( m1_subset_1 @
% 0.37/0.63                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.37/0.63                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 0.37/0.63                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 0.37/0.63                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i]:
% 0.37/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.63            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.63          ( ![B:$i]:
% 0.37/0.63            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63              ( ![C:$i]:
% 0.37/0.63                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63                  ( ![D:$i]:
% 0.37/0.63                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63                      ( ![E:$i]:
% 0.37/0.63                        ( ( m1_subset_1 @
% 0.37/0.63                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63                          ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.37/0.63                              ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 0.37/0.63                              ( m1_orders_2 @ E @ A @ D ) ) =>
% 0.37/0.63                            ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t70_orders_2])).
% 0.37/0.63  thf('0', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(t7_ordinal1, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.63  thf('2', plain, (~ (r1_tarski @ sk_D_1 @ sk_B)),
% 0.37/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(d15_orders_2, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.63                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.37/0.63                     ( ?[D:$i]:
% 0.37/0.63                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.37/0.63                         ( r2_hidden @ D @ B ) & 
% 0.37/0.63                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.37/0.63                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.63                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.37/0.63                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.63          | ((X10) = (k1_xboole_0))
% 0.37/0.63          | ((X12) = (k3_orders_2 @ X11 @ X10 @ (sk_D @ X12 @ X10 @ X11)))
% 0.37/0.63          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.37/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.63          | ~ (l1_orders_2 @ X11)
% 0.37/0.63          | ~ (v5_orders_2 @ X11)
% 0.37/0.63          | ~ (v4_orders_2 @ X11)
% 0.37/0.63          | ~ (v3_orders_2 @ X11)
% 0.37/0.63          | (v2_struct_0 @ X11))),
% 0.37/0.63      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.37/0.63          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.63  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.37/0.63          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | ((sk_E)
% 0.37/0.63            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.37/0.63        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 0.37/0.63        | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['3', '11'])).
% 0.37/0.63  thf('13', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | ((sk_E)
% 0.37/0.63            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.37/0.63        | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.63  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.37/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.63  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(t57_orders_2, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63               ( ![D:$i]:
% 0.37/0.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.37/0.63                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.37/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.63          | ~ (r2_orders_2 @ X15 @ X14 @ X17)
% 0.37/0.63          | ~ (r2_hidden @ X14 @ X16)
% 0.37/0.63          | (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 0.37/0.63          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.37/0.63          | ~ (l1_orders_2 @ X15)
% 0.37/0.63          | ~ (v5_orders_2 @ X15)
% 0.37/0.63          | ~ (v4_orders_2 @ X15)
% 0.37/0.63          | ~ (v3_orders_2 @ X15)
% 0.37/0.63          | (v2_struct_0 @ X15))),
% 0.37/0.63      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.37/0.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.37/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.63  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.37/0.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.37/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.37/0.63  thf('27', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C_1)
% 0.37/0.63          | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.37/0.63          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1))
% 0.37/0.63          | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['18', '26'])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (((v2_struct_0 @ sk_A)
% 0.37/0.63        | (r2_hidden @ sk_B @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1))
% 0.37/0.63        | ~ (r2_hidden @ sk_B @ sk_D_1)
% 0.37/0.63        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['17', '27'])).
% 0.37/0.63  thf('29', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('30', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (((v2_struct_0 @ sk_A)
% 0.37/0.63        | (r2_hidden @ sk_B @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1)))),
% 0.37/0.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.37/0.63  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      ((r2_hidden @ sk_B @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1))),
% 0.37/0.63      inference('clc', [status(thm)], ['31', '32'])).
% 0.37/0.63  thf('34', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('37', plain,
% 0.37/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.63          | ((X10) = (k1_xboole_0))
% 0.37/0.63          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.37/0.63          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.37/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.63          | ~ (l1_orders_2 @ X11)
% 0.37/0.63          | ~ (v5_orders_2 @ X11)
% 0.37/0.63          | ~ (v4_orders_2 @ X11)
% 0.37/0.63          | ~ (v3_orders_2 @ X11)
% 0.37/0.63          | (v2_struct_0 @ X11))),
% 0.37/0.63      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.37/0.63  thf('38', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.37/0.63          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ sk_D_1)
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.63  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.37/0.63          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ sk_D_1)
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.37/0.63  thf('44', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | (r2_hidden @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ sk_D_1)
% 0.37/0.63        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 0.37/0.63        | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['35', '43'])).
% 0.37/0.63  thf('45', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('46', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | (r2_hidden @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ sk_D_1)
% 0.37/0.63        | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.63  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('48', plain,
% 0.37/0.63      (((r2_hidden @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ sk_D_1)
% 0.37/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.63  thf('49', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(t4_subset, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X5 @ X6)
% 0.37/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.37/0.63          | (m1_subset_1 @ X5 @ X7))),
% 0.37/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['48', '51'])).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.37/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.63  thf('54', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('55', plain,
% 0.37/0.63      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.37/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.63          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 0.37/0.63          | (r2_orders_2 @ X15 @ X14 @ X17)
% 0.37/0.63          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.37/0.63          | ~ (l1_orders_2 @ X15)
% 0.37/0.63          | ~ (v5_orders_2 @ X15)
% 0.37/0.63          | ~ (v4_orders_2 @ X15)
% 0.37/0.63          | ~ (v3_orders_2 @ X15)
% 0.37/0.63          | (v2_struct_0 @ X15))),
% 0.37/0.63      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.37/0.63  thf('56', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.37/0.63          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.37/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.63  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('61', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.37/0.63          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.37/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.37/0.63  thf('62', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ sk_E)
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0))
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.37/0.63          | ~ (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ 
% 0.37/0.63               (u1_struct_0 @ sk_A))
% 0.37/0.63          | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['53', '61'])).
% 0.37/0.63  thf('63', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (((sk_D_1) = (k1_xboole_0))
% 0.37/0.63          | (v2_struct_0 @ sk_A)
% 0.37/0.63          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0))
% 0.37/0.63          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.37/0.63      inference('sup-', [status(thm)], ['52', '62'])).
% 0.37/0.63  thf('64', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ sk_E)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.37/0.63          | (v2_struct_0 @ sk_A)
% 0.37/0.63          | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.63  thf('65', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | (v2_struct_0 @ sk_A)
% 0.37/0.63        | (r2_orders_2 @ sk_A @ sk_C_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.37/0.63        | ~ (r2_hidden @ sk_C_1 @ sk_E))),
% 0.37/0.63      inference('sup-', [status(thm)], ['34', '64'])).
% 0.37/0.63  thf('66', plain, ((r2_hidden @ sk_C_1 @ sk_E)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('67', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | (v2_struct_0 @ sk_A)
% 0.37/0.63        | (r2_orders_2 @ sk_A @ sk_C_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))),
% 0.37/0.63      inference('demod', [status(thm)], ['65', '66'])).
% 0.37/0.63  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('69', plain,
% 0.37/0.63      (((r2_orders_2 @ sk_A @ sk_C_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.37/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['67', '68'])).
% 0.37/0.63  thf('70', plain,
% 0.37/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.37/0.63        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['48', '51'])).
% 0.37/0.63  thf('71', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(t64_orders_2, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63               ( ![D:$i]:
% 0.37/0.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63                   ( ( r2_orders_2 @ A @ B @ C ) =>
% 0.37/0.63                     ( r1_tarski @
% 0.37/0.63                       ( k3_orders_2 @ A @ D @ B ) @ 
% 0.37/0.63                       ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf('72', plain,
% 0.37/0.63      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.37/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.63          | (r1_tarski @ (k3_orders_2 @ X19 @ X20 @ X18) @ 
% 0.37/0.63             (k3_orders_2 @ X19 @ X20 @ X21))
% 0.37/0.63          | ~ (r2_orders_2 @ X19 @ X18 @ X21)
% 0.37/0.63          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.37/0.63          | ~ (l1_orders_2 @ X19)
% 0.37/0.63          | ~ (v5_orders_2 @ X19)
% 0.37/0.63          | ~ (v4_orders_2 @ X19)
% 0.37/0.63          | ~ (v3_orders_2 @ X19)
% 0.37/0.63          | (v2_struct_0 @ X19))),
% 0.37/0.63      inference('cnf', [status(esa)], [t64_orders_2])).
% 0.37/0.63  thf('73', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.63          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.37/0.63          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ X1) @ 
% 0.37/0.63             (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.37/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.63  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('75', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('78', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.47/0.63          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ X1) @ 
% 0.47/0.63             (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 0.47/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.47/0.63  thf('79', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((sk_D_1) = (k1_xboole_0))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 0.47/0.63             (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.47/0.63          | ~ (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['70', '78'])).
% 0.47/0.63  thf('80', plain,
% 0.47/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.47/0.63        | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['69', '79'])).
% 0.47/0.63  thf('81', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('82', plain,
% 0.47/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.47/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('demod', [status(thm)], ['80', '81'])).
% 0.47/0.63  thf('83', plain,
% 0.47/0.63      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63         (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['82'])).
% 0.47/0.63  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('85', plain,
% 0.47/0.63      ((((sk_D_1) = (k1_xboole_0))
% 0.47/0.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1) @ 
% 0.47/0.63           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))))),
% 0.47/0.63      inference('clc', [status(thm)], ['83', '84'])).
% 0.47/0.63  thf(d3_tarski, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.63  thf('86', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.63          | (r2_hidden @ X0 @ X2)
% 0.47/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.63  thf('87', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((sk_D_1) = (k1_xboole_0))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['85', '86'])).
% 0.47/0.63  thf('88', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ 
% 0.47/0.63         (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 0.47/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['33', '87'])).
% 0.47/0.63  thf('89', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ sk_E)
% 0.47/0.63        | ((sk_D_1) = (k1_xboole_0))
% 0.47/0.63        | ((sk_D_1) = (k1_xboole_0)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['16', '88'])).
% 0.47/0.63  thf('90', plain, ((((sk_D_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_E))),
% 0.47/0.63      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.63  thf('91', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('92', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.47/0.63      inference('clc', [status(thm)], ['90', '91'])).
% 0.47/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.63  thf('93', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.63  thf('94', plain, ($false),
% 0.47/0.63      inference('demod', [status(thm)], ['2', '92', '93'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
