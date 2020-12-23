%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PWlDMiDrdK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 684 expanded)
%              Number of leaves         :   15 ( 185 expanded)
%              Depth                    :   15
%              Number of atoms          : 1205 (15101 expanded)
%              Number of equality atoms :   22 (  68 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(t32_orders_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                     => ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_orders_2])).

thf('0',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_orders_2 @ A @ B @ C )
                      & ( r1_orders_2 @ A @ C @ D ) )
                   => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X6 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_B = sk_D )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B = sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r1_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t30_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('46',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('47',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('49',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      | ( sk_C = sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t30_orders_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,
    ( ( ( sk_C = sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_C = sk_D ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','66'])).

thf('68',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('69',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('70',plain,
    ( ( sk_C = sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','70'])).

thf('72',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('73',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('74',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('77',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('80',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('83',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('85',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('86',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('87',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( sk_B = sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('103',plain,
    ( ( sk_B = sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('105',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('107',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','75','83','84','85','86','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PWlDMiDrdK
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 145 iterations in 0.048s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.51  thf(t32_orders_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.51                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.21/0.51                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.21/0.51                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.21/0.51                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                      ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.51                            ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.21/0.51                          ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.21/0.51                            ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.21/0.51                        ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t32_orders_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.21/0.51       ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('4', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('7', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d10_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.21/0.51                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (l1_orders_2 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.51        | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.51  thf('15', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t26_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.21/0.51                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.21/0.51                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.51          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.21/0.51          | ~ (r1_orders_2 @ X4 @ X6 @ X5)
% 0.21/0.51          | ~ (r1_orders_2 @ X4 @ X3 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l1_orders_2 @ X4)
% 0.21/0.51          | ~ (v4_orders_2 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t26_orders_2])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51           | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((((r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.21/0.51         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '24'])).
% 0.21/0.51  thf('26', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | ((X0) = (X2))
% 0.21/0.51          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (l1_orders_2 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ((sk_B) = (X0))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ((sk_B) = (X0))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.21/0.51        | ((sk_B) = (sk_D))
% 0.21/0.51        | (r2_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.51  thf('33', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)) | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.51  thf('36', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t30_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ~( ( r1_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (r2_orders_2 @ X8 @ X9 @ X7)
% 0.21/0.51          | ~ (r1_orders_2 @ X8 @ X7 @ X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (l1_orders_2 @ X8)
% 0.21/0.51          | ~ (v5_orders_2 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_orders_2])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((~ (r2_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.21/0.51        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.51         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('50', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | ((X0) = (X2))
% 0.21/0.51          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (l1_orders_2 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ((sk_C) = (X0))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ((sk_C) = (X0))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | ((sk_C) = (sk_D))
% 0.21/0.51        | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((((r2_orders_2 @ sk_A @ sk_C @ sk_D) | ((sk_C) = (sk_D))))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '56'])).
% 0.21/0.51  thf('58', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (r2_orders_2 @ X8 @ X9 @ X7)
% 0.21/0.51          | ~ (r1_orders_2 @ X8 @ X7 @ X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (l1_orders_2 @ X8)
% 0.21/0.51          | ~ (v5_orders_2 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_orders_2])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_D @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_D @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((((sk_C) = (sk_D)) | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C)))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C) | ((sk_C) = (sk_D))))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((((sk_C) = (sk_B)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_B))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '24'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_B))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.51       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['71', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | ~ (r1_orders_2 @ sk_A @ sk_D @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '64'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.21/0.51             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['76', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.21/0.51       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.51       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.51       ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.51       ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['77'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.51       ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['77'])).
% 0.21/0.51  thf('88', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('89', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (l1_orders_2 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.51  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.51        | (r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '93'])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['87', '94'])).
% 0.21/0.51  thf('96', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.51           | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.51           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      ((((r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.21/0.51         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['96', '99'])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['95', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)) | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_D @ sk_C))
% 0.21/0.51         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.51             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.51       ~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.51  thf('108', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['1', '75', '83', '84', '85', '86', '107'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
