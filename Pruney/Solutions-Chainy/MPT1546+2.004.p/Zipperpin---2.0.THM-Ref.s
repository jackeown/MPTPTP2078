%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kWlJfBMUjd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 580 expanded)
%              Number of leaves         :   19 ( 170 expanded)
%              Depth                    :   20
%              Number of atoms          : 1024 (9955 expanded)
%              Number of equality atoms :   40 ( 396 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t24_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( B
                  = ( k13_lattice3 @ A @ B @ C ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( B
                    = ( k13_lattice3 @ A @ B @ C ) )
                <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_0])).

thf('0',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ~ ( v1_lattice3 @ X2 )
      | ~ ( v2_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l26_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k10_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X6 @ X5 )
      | ( r1_orders_2 @ X4 @ X3 @ ( sk_E @ X5 @ X6 @ X3 @ X4 ) )
      | ( X5
        = ( k10_lattice3 @ X4 @ X3 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v1_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v1_lattice3 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k13_lattice3 @ X9 @ X8 @ X10 )
        = ( k10_lattice3 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('31',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( X5
       != ( k10_lattice3 @ X4 @ X3 @ X6 ) )
      | ( r1_orders_2 @ X4 @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v1_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v1_lattice3 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X6 @ ( k10_lattice3 @ X4 @ X3 @ X6 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X4 @ X3 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('47',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['28'])).

thf('49',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('51',plain,(
    r1_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['29','49','50'])).

thf('52',plain,(
    r1_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['27','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('60',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','52','60'])).

thf('62',plain,
    ( ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('63',plain,(
    sk_B
 != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['29','49'])).

thf('64',plain,(
    sk_B
 != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('67',plain,(
    r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X6 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X5 @ ( sk_E @ X5 @ X6 @ X3 @ X4 ) )
      | ( X5
        = ( k10_lattice3 @ X4 @ X3 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v1_lattice3 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
      = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['58','59'])).

thf('78',plain,(
    r1_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['27','51'])).

thf('79',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf('82',plain,(
    sk_B
 != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('83',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['4','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kWlJfBMUjd
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:04:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 51 iterations in 0.056s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.53  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(t24_yellow_0, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.53         ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53               ( ( ( B ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.53                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.20/0.53            ( l1_orders_2 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                  ( ( ( B ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.53                    ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t24_yellow_0])).
% 0.20/0.53  thf('0', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_lattice3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_orders_2 @ A ) =>
% 0.20/0.53       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X2 : $i]:
% 0.20/0.53         (~ (v1_lattice3 @ X2) | ~ (v2_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.20/0.53  thf('2', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf('3', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('4', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l26_lattice3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.20/0.53         ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                   ( ( ( D ) = ( k10_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.53                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.20/0.53                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.20/0.53                       ( ![E:$i]:
% 0.20/0.53                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.20/0.53                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.20/0.53                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (r1_orders_2 @ X4 @ X3 @ X5)
% 0.20/0.53          | ~ (r1_orders_2 @ X4 @ X6 @ X5)
% 0.20/0.53          | (r1_orders_2 @ X4 @ X3 @ (sk_E @ X5 @ X6 @ X3 @ X4))
% 0.20/0.53          | ((X5) = (k10_lattice3 @ X4 @ X3 @ X6))
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (v1_lattice3 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | (v2_struct_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v1_lattice3 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.53          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.20/0.53          | ((X0) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.53  thf('15', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k13_lattice3, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ~ (l1_orders_2 @ X9)
% 0.20/0.53          | ~ (v1_lattice3 @ X9)
% 0.20/0.53          | ~ (v5_orders_2 @ X9)
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ((k13_lattice3 @ X9 @ X8 @ X10) = (k10_lattice3 @ X9 @ X8 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k13_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.53            = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v1_lattice3 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('20', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k13_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.53            = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.53         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.53          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.20/0.53          | ((X0) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A))
% 0.20/0.53        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.53         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | ((sk_B) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.53       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.53      inference('split', [status(esa)], ['28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['26'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.53         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ((X5) != (k10_lattice3 @ X4 @ X3 @ X6))
% 0.20/0.53          | (r1_orders_2 @ X4 @ X6 @ X5)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (v1_lattice3 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | (v2_struct_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | ~ (v1_lattice3 @ X4)
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.20/0.53          | (r1_orders_2 @ X4 @ X6 @ (k10_lattice3 @ X4 @ X3 @ X6))
% 0.20/0.53          | ~ (m1_subset_1 @ (k10_lattice3 @ X4 @ X3 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ (k13_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (r1_orders_2 @ sk_A @ sk_C @ (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v1_lattice3 @ sk_A)
% 0.20/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '33'])).
% 0.20/0.53  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.53         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.53  thf('37', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ (k13_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A))
% 0.20/0.53        | (r1_orders_2 @ sk_A @ sk_C @ (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['34', '35', '36', '37', '38', '39', '40'])).
% 0.20/0.53  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((r1_orders_2 @ sk_A @ sk_C @ (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | ~ (m1_subset_1 @ (k13_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.53             (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | (r1_orders_2 @ sk_A @ sk_C @ (k13_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.20/0.53         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '43'])).
% 0.20/0.53  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['26'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.53         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.20/0.53         <= (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['28'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 0.20/0.53       ~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 0.20/0.53       (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['26'])).
% 0.20/0.53  thf('51', plain, (((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['29', '49', '50'])).
% 0.20/0.53  thf('52', plain, ((r1_orders_2 @ sk_A @ sk_C @ sk_B)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['27', '51'])).
% 0.20/0.53  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t24_orders_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.53          | (r1_orders_2 @ X1 @ X0 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X1)
% 0.20/0.53          | ~ (v3_orders_2 @ X1)
% 0.20/0.53          | (v2_struct_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.53  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('60', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '52', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((((sk_B) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['28'])).
% 0.20/0.53  thf('63', plain, (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['29', '49'])).
% 0.20/0.53  thf('64', plain, (((sk_B) != (k13_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.20/0.53  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      ((r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (r1_orders_2 @ X4 @ X3 @ X5)
% 0.20/0.53          | ~ (r1_orders_2 @ X4 @ X6 @ X5)
% 0.20/0.53          | ~ (r1_orders_2 @ X4 @ X5 @ (sk_E @ X5 @ X6 @ X3 @ X4))
% 0.20/0.53          | ((X5) = (k10_lattice3 @ X4 @ X3 @ X6))
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.20/0.53          | ~ (l1_orders_2 @ X4)
% 0.20/0.53          | ~ (v1_lattice3 @ X4)
% 0.20/0.53          | ~ (v5_orders_2 @ X4)
% 0.20/0.53          | (v2_struct_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53          | ~ (v1_lattice3 @ sk_A)
% 0.20/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.53        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | ((sk_B) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '74'])).
% 0.20/0.53  thf('76', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('78', plain, ((r1_orders_2 @ sk_A @ sk_C @ sk_B)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['27', '51'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.53         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.53  thf('80', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['75', '76', '77', '78', '79', '80'])).
% 0.20/0.53  thf('82', plain, (((sk_B) != (k13_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('83', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain, ($false), inference('demod', [status(thm)], ['4', '83'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
