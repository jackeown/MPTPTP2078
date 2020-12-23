%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.egsylOdrrk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 765 expanded)
%              Number of leaves         :   15 ( 205 expanded)
%              Depth                    :   16
%              Number of atoms          : 1297 (16877 expanded)
%              Number of equality atoms :   26 (  92 expanded)
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
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
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

thf('36',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      | ( sk_C = sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
      | ( sk_C = sk_D ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('47',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
      | ( sk_C = sk_B ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_orders_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_D @ sk_C )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('59',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('60',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( sk_C = sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['47','60'])).

thf('62',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('63',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('72',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('75',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('80',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( sk_B = sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('96',plain,
    ( ( sk_B = sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('102',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B = sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_B = sk_C ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_orders_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,
    ( ( sk_B = sk_C )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','114'])).

thf('116',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('117',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','75','76','78','79','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.egsylOdrrk
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:25:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 202 iterations in 0.049s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(t32_orders_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.20/0.49                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.20/0.49                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.20/0.49                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.20/0.49                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                      ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.20/0.49                            ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.20/0.49                          ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.20/0.49                            ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.20/0.49                        ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t32_orders_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.20/0.49       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('4', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('7', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d10_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_orders_2 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.20/0.49                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l1_orders_2 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.49        | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.49  thf('15', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t26_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.20/0.49                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.20/0.49                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.49          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.20/0.49          | ~ (r1_orders_2 @ X4 @ X6 @ X5)
% 0.20/0.49          | ~ (r1_orders_2 @ X4 @ X3 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (l1_orders_2 @ X4)
% 0.20/0.49          | ~ (v4_orders_2 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t26_orders_2])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49           | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((((r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.20/0.49         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '24'])).
% 0.20/0.49  thf('26', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ((X0) = (X2))
% 0.20/0.49          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l1_orders_2 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ((sk_B) = (X0))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ((sk_B) = (X0))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.20/0.49        | ((sk_B) = (sk_D))
% 0.20/0.49        | (r2_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.49  thf('33', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)) | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ((X0) = (X2))
% 0.20/0.49          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l1_orders_2 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ((sk_C) = (X0))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ((sk_C) = (X0))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.20/0.49        | ((sk_C) = (sk_D))
% 0.20/0.49        | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((r2_orders_2 @ sk_A @ sk_C @ sk_D) | ((sk_C) = (sk_D))))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((r2_orders_2 @ sk_A @ sk_C @ sk_B) | ((sk_C) = (sk_D))))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['35', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '34'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((r2_orders_2 @ sk_A @ sk_C @ sk_B) | ((sk_C) = (sk_B))))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '34'])).
% 0.20/0.49  thf('49', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t28_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49               ( ~( ( r2_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (r2_orders_2 @ X8 @ X9 @ X7)
% 0.20/0.49          | ~ (r2_orders_2 @ X8 @ X7 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (l1_orders_2 @ X8)
% 0.20/0.49          | ~ (v5_orders_2 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t28_orders_2])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_D @ sk_C)
% 0.20/0.49        | ~ (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.49         | ~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['48', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '34'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((((sk_C) = (sk_B)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('clc', [status(thm)], ['47', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_B))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.49  thf('64', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ((X0) != (X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l1_orders_2 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ X1)
% 0.20/0.49          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['64', '66'])).
% 0.20/0.49  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('69', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.20/0.49       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['63', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '34'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['71', '72'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.20/0.49       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.49       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.20/0.49       ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.20/0.49       ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('split', [status(esa)], ['77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.49       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('81', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('82', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l1_orders_2 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.49  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.20/0.49        | (r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['81', '86'])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['80', '87'])).
% 0.20/0.49  thf('89', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.49           | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      ((((r1_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.20/0.49         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['89', '92'])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['88', '93'])).
% 0.20/0.49  thf('95', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)) | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      ((((sk_B) = (sk_D)))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.49  thf('97', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.20/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['96', '97'])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ((sk_B) = (X0))
% 0.20/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('102', plain,
% 0.20/0.49      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.49        | ((sk_B) = (sk_C))
% 0.20/0.49        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.49  thf('103', plain,
% 0.20/0.49      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C) | ((sk_B) = (sk_C))))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['99', '102'])).
% 0.20/0.49  thf('104', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['96', '97'])).
% 0.20/0.49  thf('105', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('106', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('107', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (r2_orders_2 @ X8 @ X9 @ X7)
% 0.20/0.49          | ~ (r2_orders_2 @ X8 @ X7 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (l1_orders_2 @ X8)
% 0.20/0.49          | ~ (v5_orders_2 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t28_orders_2])).
% 0.20/0.49  thf('108', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.49  thf('109', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('110', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('111', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.20/0.49  thf('112', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.49        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['105', '111'])).
% 0.20/0.49  thf('113', plain,
% 0.20/0.49      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['104', '112'])).
% 0.20/0.49  thf('114', plain,
% 0.20/0.49      ((((sk_B) = (sk_C)))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['103', '113'])).
% 0.20/0.49  thf('115', plain,
% 0.20/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_B))
% 0.20/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['98', '114'])).
% 0.20/0.49  thf('116', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.49  thf('117', plain,
% 0.20/0.49      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.49       ~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.49  thf('118', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)],
% 0.20/0.49                ['1', '70', '75', '76', '78', '79', '117'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
