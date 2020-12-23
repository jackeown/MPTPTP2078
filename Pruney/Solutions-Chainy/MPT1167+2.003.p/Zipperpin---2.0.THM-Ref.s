%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MUa2XuzcgD

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:07 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 821 expanded)
%              Number of leaves         :   27 ( 244 expanded)
%              Depth                    :   30
%              Number of atoms          : 1410 (22298 expanded)
%              Number of equality atoms :   57 ( 237 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('7',plain,(
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
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9 = k1_xboole_0 )
      | ( X11
        = ( k3_orders_2 @ X10 @ X9 @ ( sk_D @ X11 @ X9 @ X10 ) ) )
      | ~ ( m1_orders_2 @ X11 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ X0 @ sk_D_1 @ sk_A ) ) )
      | ( sk_D_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_E
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( m1_orders_2 @ X11 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
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
    inference(clc,[status(thm)],['31','32'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    | ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['34','64'])).

thf('66',plain,(
    r2_hidden @ sk_C @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) )
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k3_orders_2 @ X24 @ X25 @ X23 ) @ ( k3_orders_2 @ X24 @ X25 @ X26 ) )
      | ~ ( r2_orders_2 @ X24 @ X23 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ ( sk_D @ sk_E @ sk_D_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ sk_E )
    | ( sk_D_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','85'])).

thf('87',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ sk_E ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('88',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_E )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_B @ sk_E )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','91'])).

thf('93',plain,(
    ~ ( r2_hidden @ sk_B @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','94'])).

thf('96',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9 != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X11 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('97',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_orders_2 @ X11 @ X10 @ k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','103'])).

thf('105',plain,(
    m1_orders_2 @ sk_E @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['92','93'])).

thf('107',plain,(
    m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_E = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_E = k1_xboole_0 ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['92','93'])).

thf('113',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MUa2XuzcgD
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:23:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.43/1.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.43/1.63  % Solved by: fo/fo7.sh
% 1.43/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.63  % done 1523 iterations in 1.179s
% 1.43/1.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.43/1.63  % SZS output start Refutation
% 1.43/1.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.43/1.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.43/1.63  thf(sk_B_type, type, sk_B: $i).
% 1.43/1.63  thf(sk_E_type, type, sk_E: $i).
% 1.43/1.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.43/1.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.43/1.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.43/1.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.43/1.63  thf(sk_C_type, type, sk_C: $i).
% 1.43/1.63  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 1.43/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.43/1.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.43/1.63  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.43/1.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.43/1.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.43/1.63  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 1.43/1.63  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.43/1.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.43/1.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.43/1.63  thf(t70_orders_2, conjecture,
% 1.43/1.63    (![A:$i]:
% 1.43/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.43/1.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.43/1.63       ( ![B:$i]:
% 1.43/1.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63           ( ![C:$i]:
% 1.43/1.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63               ( ![D:$i]:
% 1.43/1.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63                   ( ![E:$i]:
% 1.43/1.63                     ( ( m1_subset_1 @
% 1.43/1.63                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 1.43/1.63                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 1.43/1.63                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 1.43/1.63                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.43/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.63    (~( ![A:$i]:
% 1.43/1.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.43/1.63            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.43/1.63          ( ![B:$i]:
% 1.43/1.63            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63              ( ![C:$i]:
% 1.43/1.63                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63                  ( ![D:$i]:
% 1.43/1.63                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63                      ( ![E:$i]:
% 1.43/1.63                        ( ( m1_subset_1 @
% 1.43/1.63                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63                          ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 1.43/1.63                              ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 1.43/1.63                              ( m1_orders_2 @ E @ A @ D ) ) =>
% 1.43/1.63                            ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 1.43/1.63    inference('cnf.neg', [status(esa)], [t70_orders_2])).
% 1.43/1.63  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('1', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('2', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('4', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('5', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf(t57_orders_2, axiom,
% 1.43/1.63    (![A:$i]:
% 1.43/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.43/1.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.43/1.63       ( ![B:$i]:
% 1.43/1.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63           ( ![C:$i]:
% 1.43/1.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63               ( ![D:$i]:
% 1.43/1.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 1.43/1.63                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.43/1.63  thf('6', plain,
% 1.43/1.63      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.43/1.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.43/1.63          | ~ (r2_orders_2 @ X20 @ X19 @ X22)
% 1.43/1.63          | ~ (r2_hidden @ X19 @ X21)
% 1.43/1.63          | (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 1.43/1.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 1.43/1.63          | ~ (l1_orders_2 @ X20)
% 1.43/1.63          | ~ (v5_orders_2 @ X20)
% 1.43/1.63          | ~ (v4_orders_2 @ X20)
% 1.43/1.63          | ~ (v3_orders_2 @ X20)
% 1.43/1.63          | (v2_struct_0 @ X20))),
% 1.43/1.63      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.43/1.63  thf('7', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (v3_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v4_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v5_orders_2 @ sk_A)
% 1.43/1.63          | ~ (l1_orders_2 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 1.43/1.63          | ~ (r2_hidden @ X1 @ sk_D_1)
% 1.43/1.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['5', '6'])).
% 1.43/1.63  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('12', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 1.43/1.63          | ~ (r2_hidden @ X1 @ sk_D_1)
% 1.43/1.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.43/1.63  thf('13', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C)
% 1.43/1.63          | ~ (r2_hidden @ X0 @ sk_D_1)
% 1.43/1.63          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 1.43/1.63          | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('sup-', [status(thm)], ['4', '12'])).
% 1.43/1.63  thf('14', plain,
% 1.43/1.63      (((v2_struct_0 @ sk_A)
% 1.43/1.63        | (r2_hidden @ sk_B @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 1.43/1.63        | ~ (r2_hidden @ sk_B @ sk_D_1)
% 1.43/1.63        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.43/1.63      inference('sup-', [status(thm)], ['3', '13'])).
% 1.43/1.63  thf('15', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('16', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('17', plain,
% 1.43/1.63      (((v2_struct_0 @ sk_A)
% 1.43/1.63        | (r2_hidden @ sk_B @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 1.43/1.63      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.43/1.63  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('19', plain, ((r2_hidden @ sk_B @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 1.43/1.63      inference('clc', [status(thm)], ['17', '18'])).
% 1.43/1.63  thf('20', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('21', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf(d15_orders_2, axiom,
% 1.43/1.63    (![A:$i]:
% 1.43/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.43/1.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.43/1.63       ( ![B:$i]:
% 1.43/1.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63           ( ![C:$i]:
% 1.43/1.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.43/1.63                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 1.43/1.63                     ( ?[D:$i]:
% 1.43/1.63                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 1.43/1.63                         ( r2_hidden @ D @ B ) & 
% 1.43/1.63                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 1.43/1.63                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.63                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 1.43/1.63                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 1.43/1.63  thf('22', plain,
% 1.43/1.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ((X9) = (k1_xboole_0))
% 1.43/1.63          | ((X11) = (k3_orders_2 @ X10 @ X9 @ (sk_D @ X11 @ X9 @ X10)))
% 1.43/1.63          | ~ (m1_orders_2 @ X11 @ X10 @ X9)
% 1.43/1.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ~ (l1_orders_2 @ X10)
% 1.43/1.63          | ~ (v5_orders_2 @ X10)
% 1.43/1.63          | ~ (v4_orders_2 @ X10)
% 1.43/1.63          | ~ (v3_orders_2 @ X10)
% 1.43/1.63          | (v2_struct_0 @ X10))),
% 1.43/1.63      inference('cnf', [status(esa)], [d15_orders_2])).
% 1.43/1.63  thf('23', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (v3_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v4_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v5_orders_2 @ sk_A)
% 1.43/1.63          | ~ (l1_orders_2 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 1.43/1.63          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['21', '22'])).
% 1.43/1.63  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('28', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 1.43/1.63          | ((X0) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ X0 @ sk_D_1 @ sk_A)))
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.43/1.63  thf('29', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | ((sk_E)
% 1.43/1.63            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 1.43/1.63        | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('sup-', [status(thm)], ['20', '28'])).
% 1.43/1.63  thf('30', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('31', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | ((sk_E)
% 1.43/1.63            = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('demod', [status(thm)], ['29', '30'])).
% 1.43/1.63  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('33', plain,
% 1.43/1.63      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('clc', [status(thm)], ['31', '32'])).
% 1.43/1.63  thf('34', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('35', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('36', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('37', plain,
% 1.43/1.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ((X9) = (k1_xboole_0))
% 1.43/1.63          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 1.43/1.63          | ~ (m1_orders_2 @ X11 @ X10 @ X9)
% 1.43/1.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ~ (l1_orders_2 @ X10)
% 1.43/1.63          | ~ (v5_orders_2 @ X10)
% 1.43/1.63          | ~ (v4_orders_2 @ X10)
% 1.43/1.63          | ~ (v3_orders_2 @ X10)
% 1.43/1.63          | (v2_struct_0 @ X10))),
% 1.43/1.63      inference('cnf', [status(esa)], [d15_orders_2])).
% 1.43/1.63  thf('38', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (v3_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v4_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v5_orders_2 @ sk_A)
% 1.43/1.63          | ~ (l1_orders_2 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 1.43/1.63          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ sk_D_1)
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['36', '37'])).
% 1.43/1.63  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('43', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.63          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 1.43/1.63          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_A) @ sk_D_1)
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 1.43/1.63  thf('44', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (r2_hidden @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ sk_D_1)
% 1.43/1.63        | ~ (m1_orders_2 @ sk_E @ sk_A @ sk_D_1)
% 1.43/1.63        | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('sup-', [status(thm)], ['35', '43'])).
% 1.43/1.63  thf('45', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('46', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (r2_hidden @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ sk_D_1)
% 1.43/1.63        | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('demod', [status(thm)], ['44', '45'])).
% 1.43/1.63  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('48', plain,
% 1.43/1.63      (((r2_hidden @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ sk_D_1)
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('clc', [status(thm)], ['46', '47'])).
% 1.43/1.63  thf('49', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf(t4_subset, axiom,
% 1.43/1.63    (![A:$i,B:$i,C:$i]:
% 1.43/1.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.43/1.63       ( m1_subset_1 @ A @ C ) ))).
% 1.43/1.63  thf('50', plain,
% 1.43/1.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.43/1.63         (~ (r2_hidden @ X6 @ X7)
% 1.43/1.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.43/1.63          | (m1_subset_1 @ X6 @ X8))),
% 1.43/1.63      inference('cnf', [status(esa)], [t4_subset])).
% 1.43/1.63  thf('51', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 1.43/1.63      inference('sup-', [status(thm)], ['49', '50'])).
% 1.43/1.63  thf('52', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['48', '51'])).
% 1.43/1.63  thf('53', plain,
% 1.43/1.63      ((((sk_E) = (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('clc', [status(thm)], ['31', '32'])).
% 1.43/1.63  thf('54', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('55', plain,
% 1.43/1.63      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.43/1.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.43/1.63          | ~ (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 1.43/1.63          | (r2_orders_2 @ X20 @ X19 @ X22)
% 1.43/1.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 1.43/1.63          | ~ (l1_orders_2 @ X20)
% 1.43/1.63          | ~ (v5_orders_2 @ X20)
% 1.43/1.63          | ~ (v4_orders_2 @ X20)
% 1.43/1.63          | ~ (v3_orders_2 @ X20)
% 1.43/1.63          | (v2_struct_0 @ X20))),
% 1.43/1.63      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.43/1.63  thf('56', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (v3_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v4_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v5_orders_2 @ sk_A)
% 1.43/1.63          | ~ (l1_orders_2 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.43/1.63          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['54', '55'])).
% 1.43/1.63  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('61', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.43/1.63          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 1.43/1.63  thf('62', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (~ (r2_hidden @ X0 @ sk_E)
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0))
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 1.43/1.63          | ~ (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ 
% 1.43/1.63               (u1_struct_0 @ sk_A))
% 1.43/1.63          | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('sup-', [status(thm)], ['53', '61'])).
% 1.43/1.63  thf('63', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (((sk_D_1) = (k1_xboole_0))
% 1.43/1.63          | (v2_struct_0 @ sk_A)
% 1.43/1.63          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0))
% 1.43/1.63          | ~ (r2_hidden @ X0 @ sk_E))),
% 1.43/1.63      inference('sup-', [status(thm)], ['52', '62'])).
% 1.43/1.63  thf('64', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (~ (r2_hidden @ X0 @ sk_E)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 1.43/1.63          | (v2_struct_0 @ sk_A)
% 1.43/1.63          | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('simplify', [status(thm)], ['63'])).
% 1.43/1.63  thf('65', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (v2_struct_0 @ sk_A)
% 1.43/1.63        | (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 1.43/1.63        | ~ (r2_hidden @ sk_C @ sk_E))),
% 1.43/1.63      inference('sup-', [status(thm)], ['34', '64'])).
% 1.43/1.63  thf('66', plain, ((r2_hidden @ sk_C @ sk_E)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('67', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (v2_struct_0 @ sk_A)
% 1.43/1.63        | (r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))),
% 1.43/1.63      inference('demod', [status(thm)], ['65', '66'])).
% 1.43/1.63  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('69', plain,
% 1.43/1.63      (((r2_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('clc', [status(thm)], ['67', '68'])).
% 1.43/1.63  thf('70', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (m1_subset_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['48', '51'])).
% 1.43/1.63  thf('71', plain,
% 1.43/1.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf(t64_orders_2, axiom,
% 1.43/1.63    (![A:$i]:
% 1.43/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.43/1.63         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.43/1.63       ( ![B:$i]:
% 1.43/1.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63           ( ![C:$i]:
% 1.43/1.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.43/1.63               ( ![D:$i]:
% 1.43/1.63                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.63                   ( ( r2_orders_2 @ A @ B @ C ) =>
% 1.43/1.63                     ( r1_tarski @
% 1.43/1.63                       ( k3_orders_2 @ A @ D @ B ) @ 
% 1.43/1.63                       ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 1.43/1.63  thf('72', plain,
% 1.43/1.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.43/1.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.43/1.63          | (r1_tarski @ (k3_orders_2 @ X24 @ X25 @ X23) @ 
% 1.43/1.63             (k3_orders_2 @ X24 @ X25 @ X26))
% 1.43/1.63          | ~ (r2_orders_2 @ X24 @ X23 @ X26)
% 1.43/1.63          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 1.43/1.63          | ~ (l1_orders_2 @ X24)
% 1.43/1.63          | ~ (v5_orders_2 @ X24)
% 1.43/1.63          | ~ (v4_orders_2 @ X24)
% 1.43/1.63          | ~ (v3_orders_2 @ X24)
% 1.43/1.63          | (v2_struct_0 @ X24))),
% 1.43/1.63      inference('cnf', [status(esa)], [t64_orders_2])).
% 1.43/1.63  thf('73', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (v3_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v4_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v5_orders_2 @ sk_A)
% 1.43/1.63          | ~ (l1_orders_2 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.43/1.63          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ X1) @ 
% 1.43/1.63             (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['71', '72'])).
% 1.43/1.63  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('75', plain, ((v4_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('78', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i]:
% 1.43/1.63         ((v2_struct_0 @ sk_A)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.43/1.63          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ X1) @ 
% 1.43/1.63             (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.43/1.63  thf('79', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (((sk_D_1) = (k1_xboole_0))
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.43/1.63          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 1.43/1.63             (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63          | ~ (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))
% 1.43/1.63          | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('sup-', [status(thm)], ['70', '78'])).
% 1.43/1.63  thf('80', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (v2_struct_0 @ sk_A)
% 1.43/1.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 1.43/1.63           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['69', '79'])).
% 1.43/1.63  thf('81', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('82', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (v2_struct_0 @ sk_A)
% 1.43/1.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 1.43/1.63           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('demod', [status(thm)], ['80', '81'])).
% 1.43/1.63  thf('83', plain,
% 1.43/1.63      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 1.43/1.63         (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A)))
% 1.43/1.63        | (v2_struct_0 @ sk_A)
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('simplify', [status(thm)], ['82'])).
% 1.43/1.63  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('85', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 1.43/1.63           (k3_orders_2 @ sk_A @ sk_D_1 @ (sk_D @ sk_E @ sk_D_1 @ sk_A))))),
% 1.43/1.63      inference('clc', [status(thm)], ['83', '84'])).
% 1.43/1.63  thf('86', plain,
% 1.43/1.63      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ sk_E)
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('sup+', [status(thm)], ['33', '85'])).
% 1.43/1.63  thf('87', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ sk_E))),
% 1.43/1.63      inference('simplify', [status(thm)], ['86'])).
% 1.43/1.63  thf(t3_subset, axiom,
% 1.43/1.63    (![A:$i,B:$i]:
% 1.43/1.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.43/1.63  thf('88', plain,
% 1.43/1.63      (![X3 : $i, X5 : $i]:
% 1.43/1.63         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.43/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.63  thf('89', plain,
% 1.43/1.63      ((((sk_D_1) = (k1_xboole_0))
% 1.43/1.63        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 1.43/1.63           (k1_zfmisc_1 @ sk_E)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['87', '88'])).
% 1.43/1.63  thf(l3_subset_1, axiom,
% 1.43/1.63    (![A:$i,B:$i]:
% 1.43/1.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.43/1.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.43/1.63  thf('90', plain,
% 1.43/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.63         (~ (r2_hidden @ X0 @ X1)
% 1.43/1.63          | (r2_hidden @ X0 @ X2)
% 1.43/1.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.43/1.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.43/1.63  thf('91', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (((sk_D_1) = (k1_xboole_0))
% 1.43/1.63          | (r2_hidden @ X0 @ sk_E)
% 1.43/1.63          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['89', '90'])).
% 1.43/1.63  thf('92', plain, (((r2_hidden @ sk_B @ sk_E) | ((sk_D_1) = (k1_xboole_0)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['19', '91'])).
% 1.43/1.63  thf('93', plain, (~ (r2_hidden @ sk_B @ sk_E)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('94', plain, (((sk_D_1) = (k1_xboole_0))),
% 1.43/1.63      inference('clc', [status(thm)], ['92', '93'])).
% 1.43/1.63  thf('95', plain,
% 1.43/1.63      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.63      inference('demod', [status(thm)], ['2', '94'])).
% 1.43/1.63  thf('96', plain,
% 1.43/1.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.43/1.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ((X9) != (k1_xboole_0))
% 1.43/1.63          | ((X11) = (k1_xboole_0))
% 1.43/1.63          | ~ (m1_orders_2 @ X11 @ X10 @ X9)
% 1.43/1.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ~ (l1_orders_2 @ X10)
% 1.43/1.63          | ~ (v5_orders_2 @ X10)
% 1.43/1.63          | ~ (v4_orders_2 @ X10)
% 1.43/1.63          | ~ (v3_orders_2 @ X10)
% 1.43/1.63          | (v2_struct_0 @ X10))),
% 1.43/1.63      inference('cnf', [status(esa)], [d15_orders_2])).
% 1.43/1.63  thf('97', plain,
% 1.43/1.63      (![X10 : $i, X11 : $i]:
% 1.43/1.63         ((v2_struct_0 @ X10)
% 1.43/1.63          | ~ (v3_orders_2 @ X10)
% 1.43/1.63          | ~ (v4_orders_2 @ X10)
% 1.43/1.63          | ~ (v5_orders_2 @ X10)
% 1.43/1.63          | ~ (l1_orders_2 @ X10)
% 1.43/1.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.43/1.63          | ~ (m1_orders_2 @ X11 @ X10 @ k1_xboole_0)
% 1.43/1.63          | ((X11) = (k1_xboole_0))
% 1.43/1.63          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 1.43/1.63      inference('simplify', [status(thm)], ['96'])).
% 1.43/1.63  thf('98', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (((X0) = (k1_xboole_0))
% 1.43/1.63          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.63          | ~ (l1_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v5_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v4_orders_2 @ sk_A)
% 1.43/1.63          | ~ (v3_orders_2 @ sk_A)
% 1.43/1.63          | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('sup-', [status(thm)], ['95', '97'])).
% 1.43/1.63  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('100', plain, ((v5_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('101', plain, ((v4_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('102', plain, ((v3_orders_2 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('103', plain,
% 1.43/1.63      (![X0 : $i]:
% 1.43/1.63         (((X0) = (k1_xboole_0))
% 1.43/1.63          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 1.43/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.63          | (v2_struct_0 @ sk_A))),
% 1.43/1.63      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 1.43/1.63  thf('104', plain,
% 1.43/1.63      (((v2_struct_0 @ sk_A)
% 1.43/1.63        | ~ (m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0)
% 1.43/1.63        | ((sk_E) = (k1_xboole_0)))),
% 1.43/1.63      inference('sup-', [status(thm)], ['1', '103'])).
% 1.43/1.63  thf('105', plain, ((m1_orders_2 @ sk_E @ sk_A @ sk_D_1)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('106', plain, (((sk_D_1) = (k1_xboole_0))),
% 1.43/1.63      inference('clc', [status(thm)], ['92', '93'])).
% 1.43/1.63  thf('107', plain, ((m1_orders_2 @ sk_E @ sk_A @ k1_xboole_0)),
% 1.43/1.63      inference('demod', [status(thm)], ['105', '106'])).
% 1.43/1.63  thf('108', plain, (((v2_struct_0 @ sk_A) | ((sk_E) = (k1_xboole_0)))),
% 1.43/1.63      inference('demod', [status(thm)], ['104', '107'])).
% 1.43/1.63  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('110', plain, (((sk_E) = (k1_xboole_0))),
% 1.43/1.63      inference('clc', [status(thm)], ['108', '109'])).
% 1.43/1.63  thf('111', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 1.43/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.63  thf('112', plain, (((sk_D_1) = (k1_xboole_0))),
% 1.43/1.63      inference('clc', [status(thm)], ['92', '93'])).
% 1.43/1.63  thf('113', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 1.43/1.63      inference('demod', [status(thm)], ['111', '112'])).
% 1.43/1.63  thf('114', plain, ($false),
% 1.43/1.63      inference('demod', [status(thm)], ['0', '110', '113'])).
% 1.43/1.63  
% 1.43/1.63  % SZS output end Refutation
% 1.43/1.63  
% 1.43/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
