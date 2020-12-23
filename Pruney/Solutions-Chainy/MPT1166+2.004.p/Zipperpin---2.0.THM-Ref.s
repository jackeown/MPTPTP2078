%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wcYVdNVduS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 797 expanded)
%              Number of leaves         :   21 ( 235 expanded)
%              Depth                    :   23
%              Number of atoms          : 1547 (16914 expanded)
%              Number of equality atoms :   62 ( 596 expanded)
%              Maximal formula depth    :   16 (   6 average)

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t69_orders_2,conjecture,(
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
             => ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ C )
                  & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( B != k1_xboole_0 )
                    & ( m1_orders_2 @ B @ A @ C )
                    & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      | ( m1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
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
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
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
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) ) ),
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
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['59','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_C
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( sk_C
    = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['79','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','109'])).

thf('111',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(irreflexivity_r2_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ~ ( r2_orders_2 @ A @ B @ B ) ) )).

thf('112',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_orders_2 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_orders_2])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','116'])).

thf('118',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','117'])).

thf('119',plain,(
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

thf('120',plain,(
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
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','126'])).

thf('128',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','116'])).

thf('130',plain,(
    m1_orders_2 @ sk_B @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['0','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wcYVdNVduS
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:40:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 74 iterations in 0.051s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(t69_orders_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                  ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50                       ( m1_orders_2 @ B @ A @ C ) & 
% 0.20/0.50                       ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t69_orders_2])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d15_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.20/0.50                     ( ?[D:$i]:
% 0.20/0.50                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.20/0.50                         ( r2_hidden @ D @ B ) & 
% 0.20/0.50                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.20/0.50                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.50                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.20/0.50                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (l1_orders_2 @ X1)
% 0.20/0.50          | ~ (v5_orders_2 @ X1)
% 0.20/0.50          | ~ (v4_orders_2 @ X1)
% 0.20/0.50          | ~ (v3_orders_2 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.20/0.50  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.50  thf('15', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (l1_orders_2 @ X1)
% 0.20/0.50          | ~ (v5_orders_2 @ X1)
% 0.20/0.50          | ~ (v4_orders_2 @ X1)
% 0.20/0.50          | ~ (v3_orders_2 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '28'])).
% 0.20/0.50  thf('30', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_D @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X2) = (k3_orders_2 @ X1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 0.20/0.50          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (l1_orders_2 @ X1)
% 0.20/0.50          | ~ (v5_orders_2 @ X1)
% 0.20/0.50          | ~ (v4_orders_2 @ X1)
% 0.20/0.50          | ~ (v3_orders_2 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.50          | ((X0) = (k3_orders_2 @ sk_A @ sk_C @ (sk_D @ X0 @ sk_C @ sk_A)))
% 0.20/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.50          | ((X0) = (k3_orders_2 @ sk_A @ sk_C @ (sk_D @ X0 @ sk_C @ sk_A)))
% 0.20/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k3_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 0.20/0.50        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '42'])).
% 0.20/0.50  thf('44', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B) = (k3_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_C @ sk_A)))
% 0.20/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t57_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.20/0.50                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.50          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 0.20/0.50          | (r2_hidden @ X10 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.20/0.50          | ~ (l1_orders_2 @ X11)
% 0.20/0.50          | ~ (v5_orders_2 @ X11)
% 0.20/0.50          | ~ (v4_orders_2 @ X11)
% 0.20/0.50          | ~ (v3_orders_2 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ X1 @ sk_C)
% 0.20/0.50          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ X1 @ sk_C)
% 0.20/0.50          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.50          | ((sk_C) = (k1_xboole_0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ X0 @ sk_C)
% 0.20/0.50          | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_C) = (k1_xboole_0))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (r2_hidden @ X0 @ sk_C)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((sk_C) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ X0 @ sk_C)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.50        | ~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X0)
% 0.20/0.50          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (l1_orders_2 @ X1)
% 0.20/0.50          | ~ (v5_orders_2 @ X1)
% 0.20/0.50          | ~ (v4_orders_2 @ X1)
% 0.20/0.50          | ~ (v3_orders_2 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.20/0.50  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '70'])).
% 0.20/0.50  thf('72', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '75'])).
% 0.20/0.50  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X2) = (k3_orders_2 @ X1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 0.20/0.51          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (l1_orders_2 @ X1)
% 0.20/0.51          | ~ (v5_orders_2 @ X1)
% 0.20/0.51          | ~ (v4_orders_2 @ X1)
% 0.20/0.51          | ~ (v3_orders_2 @ X1)
% 0.20/0.51          | (v2_struct_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.20/0.51          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.51  thf('84', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('86', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.20/0.51          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.20/0.51  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      ((((sk_C) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['80', '90'])).
% 0.20/0.51  thf('92', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      ((((sk_C) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((sk_C) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.51          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 0.20/0.51          | (r2_orders_2 @ X11 @ X10 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.20/0.51          | ~ (l1_orders_2 @ X11)
% 0.20/0.51          | ~ (v5_orders_2 @ X11)
% 0.20/0.51          | ~ (v4_orders_2 @ X11)
% 0.20/0.51          | ~ (v3_orders_2 @ X11)
% 0.20/0.51          | (v2_struct_0 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('100', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['95', '103'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['79', '106'])).
% 0.20/0.51  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      ((~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.51        | (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0))
% 0.20/0.51        | (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51           (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '109'])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf(irreflexivity_r2_orders_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ~( r2_orders_2 @ A @ B @ B ) ) ))).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (r2_orders_2 @ X7 @ X8 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.51          | ~ (l1_orders_2 @ X7)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7)))),
% 0.20/0.51      inference('cnf', [status(esa)], [irreflexivity_r2_orders_2])).
% 0.20/0.51  thf('113', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51               (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.51  thf('114', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r2_orders_2 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51               (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['113', '114'])).
% 0.20/0.51  thf('116', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_C) = (k1_xboole_0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['110', '115'])).
% 0.20/0.51  thf('117', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '116'])).
% 0.20/0.51  thf('118', plain,
% 0.20/0.51      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '117'])).
% 0.20/0.51  thf('119', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ((X0) != (k1_xboole_0))
% 0.20/0.51          | ((X2) = (k1_xboole_0))
% 0.20/0.51          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (l1_orders_2 @ X1)
% 0.20/0.51          | ~ (v5_orders_2 @ X1)
% 0.20/0.51          | ~ (v4_orders_2 @ X1)
% 0.20/0.51          | ~ (v3_orders_2 @ X1)
% 0.20/0.51          | (v2_struct_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X1)
% 0.20/0.51          | ~ (v3_orders_2 @ X1)
% 0.20/0.51          | ~ (v4_orders_2 @ X1)
% 0.20/0.51          | ~ (v5_orders_2 @ X1)
% 0.20/0.51          | ~ (l1_orders_2 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (m1_orders_2 @ X2 @ X1 @ k1_xboole_0)
% 0.20/0.51          | ((X2) = (k1_xboole_0))
% 0.20/0.51          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['119'])).
% 0.20/0.51  thf('121', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['118', '120'])).
% 0.20/0.51  thf('122', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('123', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('124', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('125', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('126', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 0.20/0.51  thf('127', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (m1_orders_2 @ sk_B @ sk_A @ k1_xboole_0)
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '126'])).
% 0.20/0.51  thf('128', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('129', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '116'])).
% 0.20/0.51  thf('130', plain, ((m1_orders_2 @ sk_B @ sk_A @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['128', '129'])).
% 0.20/0.51  thf('131', plain, (((v2_struct_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['127', '130'])).
% 0.20/0.51  thf('132', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('133', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.20/0.51  thf('134', plain, ($false), inference('demod', [status(thm)], ['0', '133'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
