%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fG35vBNnqG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:47 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 447 expanded)
%              Number of leaves         :   34 ( 135 expanded)
%              Depth                    :   24
%              Number of atoms          : 2411 (14639 expanded)
%              Number of equality atoms :   45 ( 471 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t57_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_yellow_0 @ A @ D ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r2_hidden @ D @ C )
                          & ! [E: $i] :
                              ( ( ( v1_finset_1 @ E )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                             => ~ ( ( r2_yellow_0 @ A @ E )
                                  & ( D
                                    = ( k2_yellow_0 @ A @ E ) ) ) ) ) )
                  & ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                    <=> ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r2_yellow_0 @ A @ D ) ) )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ! [E: $i] :
                                ( ( ( v1_finset_1 @ E )
                                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                               => ~ ( ( r2_yellow_0 @ A @ E )
                                    & ( D
                                      = ( k2_yellow_0 @ A @ E ) ) ) ) ) )
                    & ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ B @ D )
                      <=> ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_waybel_0])).

thf('0',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X16 @ X18 @ X17 ) @ X18 )
      | ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_D @ X16 @ X18 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X33: $i] :
      ( ( X33
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ X33 ) ) )
      | ~ ( r2_hidden @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( ( sk_D @ sk_D_2 @ X0 @ sk_A )
        = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X33 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_A ) @ sk_B )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_orders_2 @ X17 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_orders_2 @ X17 @ X16 @ ( sk_D @ X16 @ X18 @ X17 ) )
      | ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('46',plain,(
    ! [X33: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( sk_E @ X33 ) )
      | ~ ( r2_hidden @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ sk_C )
      | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C @ sk_A )
      = ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k2_yellow_0 @ X20 @ X21 ) )
      | ~ ( r1_lattice3 @ X20 @ X21 @ X23 )
      | ( r1_orders_2 @ X20 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_yellow_0 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('53',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( r2_yellow_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_orders_2 @ X20 @ X23 @ ( k2_yellow_0 @ X20 @ X21 ) )
      | ~ ( r1_lattice3 @ X20 @ X21 @ X23 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['43','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( sk_E @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['15','64'])).

thf('66',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('68',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['16'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r2_yellow_0 @ sk_A @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X9: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('79',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('81',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X32 ) @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('84',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('86',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X22
       != ( k2_yellow_0 @ X20 @ X21 ) )
      | ( r1_lattice3 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_yellow_0 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('90',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( r2_yellow_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_lattice3 @ X20 @ X21 @ ( k2_yellow_0 @ X20 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['79','93'])).

thf('95',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['16'])).

thf('97',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ sk_C )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('98',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,
    ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('105',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
               => ! [D: $i] :
                    ( ( ( r2_lattice3 @ A @ D @ B )
                     => ( r2_lattice3 @ A @ D @ C ) )
                    & ( ( r1_lattice3 @ A @ D @ C )
                     => ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_orders_2 @ X25 @ X24 @ X26 )
      | ~ ( r1_lattice3 @ X25 @ X28 @ X26 )
      | ( r1_lattice3 @ X25 @ X28 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) ) )
        | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
        | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
          = k1_xboole_0 )
        | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['95','113'])).

thf('115',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) ) @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ B @ C ) )
                & ( ( r1_orders_2 @ A @ B @ C )
                 => ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) )
                & ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ C @ B ) )
                & ( ( r1_orders_2 @ A @ C @ B )
                 => ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) )).

thf('117',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_lattice3 @ X30 @ ( k1_tarski @ X31 ) @ X29 )
      | ( r1_orders_2 @ X30 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_orders_2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['72','121'])).

thf('123',plain,
    ( ( ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('125',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
      | ( ( k1_tarski @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['123','124'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('126',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('127',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','71','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fG35vBNnqG
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.73/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.73/0.91  % Solved by: fo/fo7.sh
% 0.73/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.91  % done 530 iterations in 0.450s
% 0.73/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.73/0.91  % SZS output start Refutation
% 0.73/0.91  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.73/0.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.73/0.91  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.73/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.73/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.73/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.73/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.73/0.91  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.73/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.73/0.91  thf(sk_E_type, type, sk_E: $i > $i).
% 0.73/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.73/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.73/0.91  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.73/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.73/0.91  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.73/0.91  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.73/0.91  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.73/0.91  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.73/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.91  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.73/0.91  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.73/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.91  thf(t57_waybel_0, conjecture,
% 0.73/0.91    (![A:$i]:
% 0.73/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.73/0.91         ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.73/0.91       ( ![B:$i]:
% 0.73/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.73/0.91           ( ![C:$i]:
% 0.73/0.91             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.73/0.91               ( ( ( ![D:$i]:
% 0.73/0.91                     ( ( ( v1_finset_1 @ D ) & 
% 0.73/0.91                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.73/0.91                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.73/0.91                         ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.73/0.91                   ( ![D:$i]:
% 0.73/0.91                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91                       ( ~( ( r2_hidden @ D @ C ) & 
% 0.73/0.91                            ( ![E:$i]:
% 0.73/0.91                              ( ( ( v1_finset_1 @ E ) & 
% 0.73/0.91                                  ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.73/0.91                                ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.73/0.91                                     ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.73/0.91                   ( ![D:$i]:
% 0.73/0.91                     ( ( ( v1_finset_1 @ D ) & 
% 0.73/0.91                         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.73/0.91                       ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.73/0.91                         ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.73/0.91                 ( ![D:$i]:
% 0.73/0.91                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91                     ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.73/0.91                       ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.91    (~( ![A:$i]:
% 0.73/0.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.73/0.91            ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.73/0.91          ( ![B:$i]:
% 0.73/0.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.73/0.91              ( ![C:$i]:
% 0.73/0.91                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.73/0.91                  ( ( ( ![D:$i]:
% 0.73/0.91                        ( ( ( v1_finset_1 @ D ) & 
% 0.73/0.91                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.73/0.91                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.73/0.91                            ( r2_yellow_0 @ A @ D ) ) ) ) & 
% 0.73/0.91                      ( ![D:$i]:
% 0.73/0.91                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91                          ( ~( ( r2_hidden @ D @ C ) & 
% 0.73/0.91                               ( ![E:$i]:
% 0.73/0.91                                 ( ( ( v1_finset_1 @ E ) & 
% 0.73/0.91                                     ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.73/0.91                                   ( ~( ( r2_yellow_0 @ A @ E ) & 
% 0.73/0.91                                        ( ( D ) = ( k2_yellow_0 @ A @ E ) ) ) ) ) ) ) ) ) ) & 
% 0.73/0.91                      ( ![D:$i]:
% 0.73/0.91                        ( ( ( v1_finset_1 @ D ) & 
% 0.73/0.91                            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.73/0.91                          ( ( ( D ) != ( k1_xboole_0 ) ) =>
% 0.73/0.91                            ( r2_hidden @ ( k2_yellow_0 @ A @ D ) @ C ) ) ) ) ) =>
% 0.73/0.91                    ( ![D:$i]:
% 0.73/0.91                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91                        ( ( r1_lattice3 @ A @ B @ D ) <=>
% 0.73/0.91                          ( r1_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.73/0.91    inference('cnf.neg', [status(esa)], [t57_waybel_0])).
% 0.73/0.91  thf('0', plain,
% 0.73/0.91      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | ~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('1', plain,
% 0.73/0.91      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.73/0.91       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('split', [status(esa)], ['0'])).
% 0.73/0.91  thf('2', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(d8_lattice3, axiom,
% 0.73/0.91    (![A:$i]:
% 0.73/0.91     ( ( l1_orders_2 @ A ) =>
% 0.73/0.91       ( ![B:$i,C:$i]:
% 0.73/0.91         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.73/0.91             ( ![D:$i]:
% 0.73/0.91               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.73/0.91  thf('3', plain,
% 0.73/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.73/0.91          | (r2_hidden @ (sk_D @ X16 @ X18 @ X17) @ X18)
% 0.73/0.91          | (r1_lattice3 @ X17 @ X18 @ X16)
% 0.73/0.91          | ~ (l1_orders_2 @ X17))),
% 0.73/0.91      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.73/0.91  thf('4', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ sk_A)
% 0.73/0.91          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.73/0.91      inference('sup-', [status(thm)], ['2', '3'])).
% 0.73/0.91  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('6', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.73/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('7', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('8', plain,
% 0.73/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ X16 @ X18 @ X17) @ (u1_struct_0 @ X17))
% 0.73/0.91          | (r1_lattice3 @ X17 @ X18 @ X16)
% 0.73/0.91          | ~ (l1_orders_2 @ X17))),
% 0.73/0.91      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.73/0.91  thf('9', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ sk_A)
% 0.73/0.91          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.73/0.91  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('11', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.73/0.91  thf('12', plain,
% 0.73/0.91      (![X33 : $i]:
% 0.73/0.91         (((X33) = (k2_yellow_0 @ sk_A @ (sk_E @ X33)))
% 0.73/0.91          | ~ (r2_hidden @ X33 @ sk_C)
% 0.73/0.91          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('13', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.73/0.91          | ((sk_D @ sk_D_2 @ X0 @ sk_A)
% 0.73/0.91              = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)))))),
% 0.73/0.91      inference('sup-', [status(thm)], ['11', '12'])).
% 0.73/0.91  thf('14', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | ((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.73/0.91            = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['6', '13'])).
% 0.73/0.91  thf('15', plain,
% 0.73/0.91      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.73/0.91          = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['14'])).
% 0.73/0.91  thf('16', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('17', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('split', [status(esa)], ['16'])).
% 0.73/0.91  thf('18', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.73/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('19', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.73/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('20', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.73/0.91  thf('21', plain,
% 0.73/0.91      (![X33 : $i]:
% 0.73/0.91         ((m1_subset_1 @ (sk_E @ X33) @ (k1_zfmisc_1 @ sk_B))
% 0.73/0.91          | ~ (r2_hidden @ X33 @ sk_C)
% 0.73/0.91          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('22', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.73/0.91          | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.73/0.91             (k1_zfmisc_1 @ sk_B)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['20', '21'])).
% 0.73/0.91  thf('23', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | (m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.73/0.91           (k1_zfmisc_1 @ sk_B))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['19', '22'])).
% 0.73/0.91  thf('24', plain,
% 0.73/0.91      (((m1_subset_1 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.73/0.91         (k1_zfmisc_1 @ sk_B))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['23'])).
% 0.73/0.91  thf(l3_subset_1, axiom,
% 0.73/0.91    (![A:$i,B:$i]:
% 0.73/0.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.73/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.73/0.91  thf('25', plain,
% 0.73/0.91      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X1 @ X2)
% 0.73/0.91          | (r2_hidden @ X1 @ X3)
% 0.73/0.91          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.73/0.91      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.73/0.91  thf('26', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ X0 @ sk_B)
% 0.73/0.91          | ~ (r2_hidden @ X0 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 0.73/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.73/0.91  thf('27', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2)
% 0.73/0.91        | (r2_hidden @ 
% 0.73/0.91           (sk_D @ sk_D_2 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_A) @ 
% 0.73/0.91           sk_B)
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['18', '26'])).
% 0.73/0.91  thf('28', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.73/0.91  thf('29', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('30', plain,
% 0.73/0.91      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.73/0.91          | ~ (r1_lattice3 @ X17 @ X18 @ X16)
% 0.73/0.91          | ~ (r2_hidden @ X19 @ X18)
% 0.73/0.91          | (r1_orders_2 @ X17 @ X16 @ X19)
% 0.73/0.91          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.73/0.91          | ~ (l1_orders_2 @ X17))),
% 0.73/0.91      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.73/0.91  thf('31', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ sk_A)
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.73/0.91          | ~ (r2_hidden @ X0 @ X1)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.73/0.91  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('33', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.73/0.91          | ~ (r2_hidden @ X0 @ X1)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.73/0.91      inference('demod', [status(thm)], ['31', '32'])).
% 0.73/0.91  thf('34', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.73/0.91          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['28', '33'])).
% 0.73/0.91  thf('35', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2)
% 0.73/0.91        | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91           (sk_D @ sk_D_2 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_A))
% 0.73/0.91        | ~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['27', '34'])).
% 0.73/0.91  thf('36', plain,
% 0.73/0.91      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91           (sk_D @ sk_D_2 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_A))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2)
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['35'])).
% 0.73/0.91  thf('37', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ 
% 0.73/0.91            sk_D_2)
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91            (sk_D @ sk_D_2 @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_A))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['17', '36'])).
% 0.73/0.91  thf('38', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('39', plain,
% 0.73/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.73/0.91          | ~ (r1_orders_2 @ X17 @ X16 @ (sk_D @ X16 @ X18 @ X17))
% 0.73/0.91          | (r1_lattice3 @ X17 @ X18 @ X16)
% 0.73/0.91          | ~ (l1_orders_2 @ X17))),
% 0.73/0.91      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.73/0.91  thf('40', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ sk_A)
% 0.73/0.91          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.73/0.91  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('42', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['40', '41'])).
% 0.73/0.91  thf('43', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('clc', [status(thm)], ['37', '42'])).
% 0.73/0.91  thf('44', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.73/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('45', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.73/0.91  thf('46', plain,
% 0.73/0.91      (![X33 : $i]:
% 0.73/0.91         ((r2_yellow_0 @ sk_A @ (sk_E @ X33))
% 0.73/0.91          | ~ (r2_hidden @ X33 @ sk_C)
% 0.73/0.91          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('47', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ sk_C)
% 0.73/0.91          | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ X0 @ sk_A))))),
% 0.73/0.91      inference('sup-', [status(thm)], ['45', '46'])).
% 0.73/0.91  thf('48', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['44', '47'])).
% 0.73/0.91  thf('49', plain,
% 0.73/0.91      (((r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['48'])).
% 0.73/0.91  thf('50', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.73/0.91  thf('51', plain,
% 0.73/0.91      ((((sk_D @ sk_D_2 @ sk_C @ sk_A)
% 0.73/0.91          = (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['14'])).
% 0.73/0.91  thf(d10_yellow_0, axiom,
% 0.73/0.91    (![A:$i]:
% 0.73/0.91     ( ( l1_orders_2 @ A ) =>
% 0.73/0.91       ( ![B:$i,C:$i]:
% 0.73/0.91         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91           ( ( r2_yellow_0 @ A @ B ) =>
% 0.73/0.91             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.73/0.91               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.73/0.91                 ( ![D:$i]:
% 0.73/0.91                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.73/0.91                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.91  thf('52', plain,
% 0.73/0.91      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.73/0.91         (((X22) != (k2_yellow_0 @ X20 @ X21))
% 0.73/0.91          | ~ (r1_lattice3 @ X20 @ X21 @ X23)
% 0.73/0.91          | (r1_orders_2 @ X20 @ X23 @ X22)
% 0.73/0.91          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.73/0.91          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.73/0.91          | ~ (r2_yellow_0 @ X20 @ X21)
% 0.73/0.91          | ~ (l1_orders_2 @ X20))),
% 0.73/0.91      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.73/0.91  thf('53', plain,
% 0.73/0.91      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ X20)
% 0.73/0.91          | ~ (r2_yellow_0 @ X20 @ X21)
% 0.73/0.91          | ~ (m1_subset_1 @ (k2_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20))
% 0.73/0.91          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.73/0.91          | (r1_orders_2 @ X20 @ X23 @ (k2_yellow_0 @ X20 @ X21))
% 0.73/0.91          | ~ (r1_lattice3 @ X20 @ X21 @ X23))),
% 0.73/0.91      inference('simplify', [status(thm)], ['52'])).
% 0.73/0.91  thf('54', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.73/0.91          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.73/0.91          | ~ (l1_orders_2 @ sk_A))),
% 0.73/0.91      inference('sup-', [status(thm)], ['51', '53'])).
% 0.73/0.91  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('56', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.73/0.91          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))),
% 0.73/0.91      inference('demod', [status(thm)], ['54', '55'])).
% 0.73/0.91  thf('57', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.73/0.91          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['50', '56'])).
% 0.73/0.91  thf('58', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.73/0.91          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | ~ (r2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['57'])).
% 0.73/0.91  thf('59', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0))),
% 0.73/0.91      inference('sup-', [status(thm)], ['49', '58'])).
% 0.73/0.91  thf('60', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (r1_lattice3 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A)) @ X0)
% 0.73/0.91          | (r1_orders_2 @ sk_A @ X0 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.73/0.91      inference('simplify', [status(thm)], ['59'])).
% 0.73/0.91  thf('61', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['43', '60'])).
% 0.73/0.91  thf('62', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('63', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91            (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('demod', [status(thm)], ['61', '62'])).
% 0.73/0.91  thf('64', plain,
% 0.73/0.91      ((((r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91          (k2_yellow_0 @ sk_A @ (sk_E @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['63'])).
% 0.73/0.91  thf('65', plain,
% 0.73/0.91      ((((r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('sup+', [status(thm)], ['15', '64'])).
% 0.73/0.91  thf('66', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_A))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['65'])).
% 0.73/0.91  thf('67', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['40', '41'])).
% 0.73/0.91  thf('68', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('clc', [status(thm)], ['66', '67'])).
% 0.73/0.91  thf('69', plain,
% 0.73/0.91      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.73/0.91         <= (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('split', [status(esa)], ['0'])).
% 0.73/0.91  thf('70', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.73/0.91       ~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['68', '69'])).
% 0.73/0.91  thf('71', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.73/0.91       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('split', [status(esa)], ['16'])).
% 0.73/0.91  thf('72', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.73/0.91  thf('73', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.73/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf(t63_subset_1, axiom,
% 0.73/0.91    (![A:$i,B:$i]:
% 0.73/0.91     ( ( r2_hidden @ A @ B ) =>
% 0.73/0.91       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.73/0.91  thf('74', plain,
% 0.73/0.91      (![X4 : $i, X5 : $i]:
% 0.73/0.91         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 0.73/0.91          | ~ (r2_hidden @ X4 @ X5))),
% 0.73/0.91      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.73/0.91  thf('75', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.73/0.91             (k1_zfmisc_1 @ X0)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['73', '74'])).
% 0.73/0.91  thf('76', plain,
% 0.73/0.91      (![X34 : $i]:
% 0.73/0.91         (((X34) = (k1_xboole_0))
% 0.73/0.91          | (r2_yellow_0 @ sk_A @ X34)
% 0.73/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ sk_B))
% 0.73/0.91          | ~ (v1_finset_1 @ X34))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('77', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.73/0.91        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['75', '76'])).
% 0.73/0.91  thf(fc1_finset_1, axiom, (![A:$i]: ( v1_finset_1 @ ( k1_tarski @ A ) ))).
% 0.73/0.91  thf('78', plain, (![X9 : $i]: (v1_finset_1 @ (k1_tarski @ X9))),
% 0.73/0.91      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.73/0.91  thf('79', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('demod', [status(thm)], ['77', '78'])).
% 0.73/0.91  thf('80', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | (m1_subset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ X0 @ sk_A)) @ 
% 0.73/0.91             (k1_zfmisc_1 @ X0)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['73', '74'])).
% 0.73/0.91  thf('81', plain,
% 0.73/0.91      (![X32 : $i]:
% 0.73/0.91         (((X32) = (k1_xboole_0))
% 0.73/0.91          | (r2_hidden @ (k2_yellow_0 @ sk_A @ X32) @ sk_C)
% 0.73/0.91          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ sk_B))
% 0.73/0.91          | ~ (v1_finset_1 @ X32))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('82', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | ~ (v1_finset_1 @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.73/0.91        | (r2_hidden @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91           sk_C)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['80', '81'])).
% 0.73/0.91  thf('83', plain, (![X9 : $i]: (v1_finset_1 @ (k1_tarski @ X9))),
% 0.73/0.91      inference('cnf', [status(esa)], [fc1_finset_1])).
% 0.73/0.91  thf('84', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r2_hidden @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91           sk_C)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('demod', [status(thm)], ['82', '83'])).
% 0.73/0.91  thf('85', plain,
% 0.73/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(t4_subset, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.73/0.91       ( m1_subset_1 @ A @ C ) ))).
% 0.73/0.91  thf('86', plain,
% 0.73/0.91      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.73/0.91         (~ (r2_hidden @ X6 @ X7)
% 0.73/0.91          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.73/0.91          | (m1_subset_1 @ X6 @ X8))),
% 0.73/0.91      inference('cnf', [status(esa)], [t4_subset])).
% 0.73/0.91  thf('87', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.73/0.91      inference('sup-', [status(thm)], ['85', '86'])).
% 0.73/0.91  thf('88', plain,
% 0.73/0.91      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (m1_subset_1 @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91           (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['84', '87'])).
% 0.73/0.91  thf('89', plain,
% 0.73/0.91      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.73/0.91         (((X22) != (k2_yellow_0 @ X20 @ X21))
% 0.73/0.91          | (r1_lattice3 @ X20 @ X21 @ X22)
% 0.73/0.91          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.73/0.91          | ~ (r2_yellow_0 @ X20 @ X21)
% 0.73/0.91          | ~ (l1_orders_2 @ X20))),
% 0.73/0.91      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.73/0.91  thf('90', plain,
% 0.73/0.91      (![X20 : $i, X21 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ X20)
% 0.73/0.91          | ~ (r2_yellow_0 @ X20 @ X21)
% 0.73/0.91          | ~ (m1_subset_1 @ (k2_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20))
% 0.73/0.91          | (r1_lattice3 @ X20 @ X21 @ (k2_yellow_0 @ X20 @ X21)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['89'])).
% 0.73/0.91  thf('91', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))
% 0.73/0.91        | ~ (l1_orders_2 @ sk_A))),
% 0.73/0.91      inference('sup-', [status(thm)], ['88', '90'])).
% 0.73/0.91  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('93', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91        | ~ (r2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))),
% 0.73/0.91      inference('demod', [status(thm)], ['91', '92'])).
% 0.73/0.91  thf('94', plain,
% 0.73/0.91      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['79', '93'])).
% 0.73/0.91  thf('95', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.73/0.91         (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['94'])).
% 0.73/0.91  thf('96', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('split', [status(esa)], ['16'])).
% 0.73/0.91  thf('97', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r2_hidden @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91           sk_C)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('demod', [status(thm)], ['82', '83'])).
% 0.73/0.91  thf('98', plain,
% 0.73/0.91      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (m1_subset_1 @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91           (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['84', '87'])).
% 0.73/0.91  thf('99', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.73/0.91          | ~ (r2_hidden @ X0 @ X1)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.73/0.91      inference('demod', [status(thm)], ['31', '32'])).
% 0.73/0.91  thf('100', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91          | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r2_hidden @ 
% 0.73/0.91               (k2_yellow_0 @ sk_A @ 
% 0.73/0.91                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91               X0)
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91             (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)))))),
% 0.73/0.91      inference('sup-', [status(thm)], ['98', '99'])).
% 0.73/0.91  thf('101', plain,
% 0.73/0.91      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91        | ~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['97', '100'])).
% 0.73/0.91  thf('102', plain,
% 0.73/0.91      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.73/0.91        | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['101'])).
% 0.73/0.91  thf('103', plain,
% 0.73/0.91      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91            (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['96', '102'])).
% 0.73/0.91  thf('104', plain,
% 0.73/0.91      ((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91        | (m1_subset_1 @ 
% 0.73/0.91           (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))) @ 
% 0.73/0.91           (u1_struct_0 @ sk_A)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['84', '87'])).
% 0.73/0.91  thf('105', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(t4_yellow_0, axiom,
% 0.73/0.91    (![A:$i]:
% 0.73/0.91     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.73/0.91       ( ![B:$i]:
% 0.73/0.91         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91           ( ![C:$i]:
% 0.73/0.91             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91               ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.73/0.91                 ( ![D:$i]:
% 0.73/0.91                   ( ( ( r2_lattice3 @ A @ D @ B ) =>
% 0.73/0.91                       ( r2_lattice3 @ A @ D @ C ) ) & 
% 0.73/0.91                     ( ( r1_lattice3 @ A @ D @ C ) =>
% 0.73/0.91                       ( r1_lattice3 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.91  thf('106', plain,
% 0.73/0.91      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.73/0.91          | ~ (r1_orders_2 @ X25 @ X24 @ X26)
% 0.73/0.91          | ~ (r1_lattice3 @ X25 @ X28 @ X26)
% 0.73/0.91          | (r1_lattice3 @ X25 @ X28 @ X24)
% 0.73/0.91          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.73/0.91          | ~ (l1_orders_2 @ X25)
% 0.73/0.91          | ~ (v4_orders_2 @ X25))),
% 0.73/0.91      inference('cnf', [status(esa)], [t4_yellow_0])).
% 0.73/0.91  thf('107', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         (~ (v4_orders_2 @ sk_A)
% 0.73/0.91          | ~ (l1_orders_2 @ sk_A)
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X1 @ X0)
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.73/0.91      inference('sup-', [status(thm)], ['105', '106'])).
% 0.73/0.91  thf('108', plain, ((v4_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('109', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('110', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X1 @ X0)
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.73/0.91      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.73/0.91  thf('111', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91          | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ 
% 0.73/0.91               (k2_yellow_0 @ sk_A @ 
% 0.73/0.91                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.73/0.91               (k2_yellow_0 @ sk_A @ 
% 0.73/0.91                (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['104', '110'])).
% 0.73/0.91  thf('112', plain,
% 0.73/0.91      ((![X0 : $i]:
% 0.73/0.91          ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91           | ~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.73/0.91                (k2_yellow_0 @ sk_A @ 
% 0.73/0.91                 (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91           | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['103', '111'])).
% 0.73/0.91  thf('113', plain,
% 0.73/0.91      ((![X0 : $i]:
% 0.73/0.91          (~ (r1_lattice3 @ sk_A @ X0 @ 
% 0.73/0.91              (k2_yellow_0 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A))))
% 0.73/0.91           | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91           | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91           | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['112'])).
% 0.73/0.91  thf('114', plain,
% 0.73/0.91      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.73/0.91            sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['95', '113'])).
% 0.73/0.91  thf('115', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ (k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) @ 
% 0.73/0.91          sk_D_2)
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['114'])).
% 0.73/0.91  thf('116', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(t7_yellow_0, axiom,
% 0.73/0.91    (![A:$i]:
% 0.73/0.91     ( ( l1_orders_2 @ A ) =>
% 0.73/0.91       ( ![B:$i]:
% 0.73/0.91         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91           ( ![C:$i]:
% 0.73/0.91             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.91               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.73/0.91                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.73/0.91                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.73/0.91                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.73/0.91                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.73/0.91                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.73/0.91                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.73/0.91                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.73/0.91  thf('117', plain,
% 0.73/0.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.73/0.91          | ~ (r1_lattice3 @ X30 @ (k1_tarski @ X31) @ X29)
% 0.73/0.91          | (r1_orders_2 @ X30 @ X29 @ X31)
% 0.73/0.91          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.73/0.91          | ~ (l1_orders_2 @ X30))),
% 0.73/0.91      inference('cnf', [status(esa)], [t7_yellow_0])).
% 0.73/0.91  thf('118', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (l1_orders_2 @ sk_A)
% 0.73/0.91          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['116', '117'])).
% 0.73/0.91  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf('120', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.73/0.91          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.73/0.91          | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_D_2))),
% 0.73/0.91      inference('demod', [status(thm)], ['118', '119'])).
% 0.73/0.91  thf('121', plain,
% 0.73/0.91      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.73/0.91         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ 
% 0.73/0.91              (u1_struct_0 @ sk_A))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['115', '120'])).
% 0.73/0.91  thf('122', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['72', '121'])).
% 0.73/0.91  thf('123', plain,
% 0.73/0.91      (((((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.73/0.91         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.73/0.91         | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('simplify', [status(thm)], ['122'])).
% 0.73/0.91  thf('124', plain,
% 0.73/0.91      (![X0 : $i]:
% 0.73/0.91         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.73/0.91          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.73/0.91      inference('demod', [status(thm)], ['40', '41'])).
% 0.73/0.91  thf('125', plain,
% 0.73/0.91      ((((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.73/0.91         | ((k1_tarski @ (sk_D @ sk_D_2 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('clc', [status(thm)], ['123', '124'])).
% 0.73/0.91  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.73/0.91  thf('126', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.73/0.91      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.73/0.91  thf('127', plain,
% 0.73/0.91      (((~ (v1_xboole_0 @ k1_xboole_0) | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('sup-', [status(thm)], ['125', '126'])).
% 0.73/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.73/0.91  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.73/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.73/0.91  thf('129', plain,
% 0.73/0.91      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.73/0.91         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.73/0.91      inference('demod', [status(thm)], ['127', '128'])).
% 0.73/0.91  thf('130', plain,
% 0.73/0.91      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.73/0.91         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.73/0.91      inference('split', [status(esa)], ['0'])).
% 0.73/0.91  thf('131', plain,
% 0.73/0.91      (~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.73/0.91       ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.73/0.91      inference('sup-', [status(thm)], ['129', '130'])).
% 0.73/0.91  thf('132', plain, ($false),
% 0.73/0.91      inference('sat_resolution*', [status(thm)], ['1', '70', '71', '131'])).
% 0.73/0.91  
% 0.73/0.91  % SZS output end Refutation
% 0.73/0.91  
% 0.73/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
