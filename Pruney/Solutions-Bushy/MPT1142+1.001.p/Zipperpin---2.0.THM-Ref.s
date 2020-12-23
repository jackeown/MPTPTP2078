%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1142+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OvO3nbnnxM

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 775 expanded)
%              Number of leaves         :   15 ( 208 expanded)
%              Depth                    :   15
%              Number of atoms          : 1221 (16995 expanded)
%              Number of equality atoms :   32 ( 100 expanded)
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

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( r1_orders_2 @ X7 @ X6 @ X8 )
      | ~ ( r1_orders_2 @ X7 @ X9 @ X8 )
      | ~ ( r1_orders_2 @ X7 @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
    | ( sk_B = sk_D )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B = sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('47',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('49',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X5 @ X3 )
      | ( X3 = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,
    ( ( ( sk_C = sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_C = sk_D ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('62',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('63',plain,
    ( ( sk_C = sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('73',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,
    ( ( sk_B = sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('84',plain,
    ( ( sk_B = sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('86',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('88',plain,
    ( ( ( sk_C = sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('89',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_C = sk_D ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('91',plain,
    ( ( sk_B = sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('92',plain,
    ( ( sk_C = sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','92'])).

thf('94',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('95',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('97',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('99',plain,
    ( ( ( sk_C = sk_D )
      | ~ ( r1_orders_2 @ sk_A @ sk_D @ sk_C ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_C = sk_D ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('102',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('103',plain,
    ( ( sk_C = sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('105',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('107',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('109',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['71','72','73','75','95','107','108'])).


%------------------------------------------------------------------------------
