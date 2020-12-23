%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a4M0NHfIMM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 186 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  715 (4056 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
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
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B = sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_B = sk_C ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r2_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r2_orders_2 @ X4 @ X6 @ X5 )
      | ~ ( r2_orders_2 @ X4 @ X3 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t29_orders_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( sk_B = sk_C )
        | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      | ( sk_B = sk_C ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( sk_B = sk_C )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = sk_C )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 )
        | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('43',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
      | ( sk_C = sk_D ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,
    ( ( sk_C = sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('57',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_D )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','41','42','43','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a4M0NHfIMM
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 108 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.49  thf(t32_orders_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.49                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.21/0.49                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.21/0.49                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.21/0.49                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                      ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.49                            ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.21/0.49                          ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.21/0.49                            ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.21/0.49                        ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t32_orders_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.21/0.49       ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('7', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d10_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.21/0.49                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.49          | ((X0) = (X2))
% 0.21/0.49          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (l1_orders_2 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49          | ((sk_B) = (X0))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49          | ((sk_B) = (X0))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.49        | ((sk_B) = (sk_C))
% 0.21/0.49        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C) | ((sk_B) = (sk_C))))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.49  thf('15', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t29_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49                   ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.21/0.49                       ( r2_orders_2 @ A @ C @ D ) ) =>
% 0.21/0.49                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.49          | (r2_orders_2 @ X4 @ X3 @ X5)
% 0.21/0.49          | ~ (r2_orders_2 @ X4 @ X6 @ X5)
% 0.21/0.49          | ~ (r2_orders_2 @ X4 @ X3 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (l1_orders_2 @ X4)
% 0.21/0.49          | ~ (v5_orders_2 @ X4)
% 0.21/0.49          | ~ (v4_orders_2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_orders_2])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (((sk_B) = (sk_C))
% 0.21/0.49           | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.49           | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((r2_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.21/0.49         | ~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.49         | ((sk_B) = (sk_C)))) <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '24'])).
% 0.21/0.49  thf('26', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((((sk_B) = (sk_C)) | ~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((sk_B) = (sk_C)))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.49             ((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.49       ~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('34', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '22'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.49           | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((r2_orders_2 @ sk_A @ sk_B @ sk_D)
% 0.21/0.49         | ~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.49  thf('39', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.49       ~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.49       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.49       ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['44'])).
% 0.21/0.49  thf('46', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.49          | ((X0) = (X2))
% 0.21/0.49          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (l1_orders_2 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.49          | ((sk_C) = (X0))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.49          | ((sk_C) = (X0))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.49        | ((sk_C) = (sk_D))
% 0.21/0.49        | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((((r2_orders_2 @ sk_A @ sk_C @ sk_D) | ((sk_C) = (sk_D))))
% 0.21/0.49         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((sk_C) = (sk_D)))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((r2_orders_2 @ sk_A @ sk_B @ sk_D))
% 0.21/0.49         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.49             ((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.49       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf('60', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)],
% 0.21/0.49                ['1', '32', '41', '42', '43', '59'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
