%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1656+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3y2zQfT7pE

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:56 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  207 (13477 expanded)
%              Number of leaves         :   29 (3567 expanded)
%              Depth                    :   53
%              Number of atoms          : 2577 (242163 expanded)
%              Number of equality atoms :    4 ( 155 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t36_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattice3 @ A @ B @ C )
              <=> ( r1_lattice3 @ A @ ( k4_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_lattice3 @ A @ B @ C )
                <=> ( r1_lattice3 @ A @ ( k4_waybel_0 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_waybel_0])).

thf('0',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X13 @ X12 ) @ X13 )
      | ( r1_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X11 @ X13 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r3_orders_2 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ X17 @ X19 )
      | ~ ( r3_orders_2 @ X18 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d16_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k4_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                          & ( r1_orders_2 @ A @ E @ D )
                          & ( r2_hidden @ E @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r2_hidden @ E @ B )
        & ( r1_orders_2 @ A @ E @ D )
        & ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X2 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k4_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k4_waybel_0 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_0])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k4_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k4_waybel_0 @ X6 @ X5 ) )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ( r2_hidden @ X8 @ ( k4_waybel_0 @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_orders_2 @ X12 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ X11 @ ( sk_D_1 @ X11 @ X13 @ X12 ) )
      | ( r1_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(clc,[status(thm)],['66','71'])).

thf('73',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
   <= ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','72'])).

thf('74',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','75'])).

thf('77',plain,(
    ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('82',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k4_waybel_0 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_0])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ( r2_hidden @ X8 @ ( k4_waybel_0 @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('94',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,(
    ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('97',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('99',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( r3_orders_2 @ X18 @ X17 @ X19 )
      | ~ ( r1_orders_2 @ X18 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','106'])).

thf('108',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('109',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('111',plain,
    ( ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('115',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ X17 @ X19 )
      | ~ ( r3_orders_2 @ X18 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,
    ( ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','128'])).

thf('130',plain,(
    ~ ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('131',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('135',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k4_waybel_0 @ X6 @ X5 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X8 @ X5 @ X6 ) @ X8 @ X5 @ X6 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('136',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_hidden @ X8 @ ( k4_waybel_0 @ X6 @ X5 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X8 @ X5 @ X6 ) @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('142',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','143'])).

thf('145',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['133','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ X3 @ X0 @ X2 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('147',plain,(
    r1_orders_2 @ sk_A @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['133','144'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,(
    m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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

thf('152',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_orders_2 @ X24 @ X23 @ X25 )
      | ~ ( r1_orders_2 @ X24 @ X26 @ X25 )
      | ~ ( r1_orders_2 @ X24 @ X23 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_orders_2])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','156'])).

thf('158',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['133','144'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('160',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    m1_subset_1 @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('166',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('167',plain,(
    r1_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','75','166'])).

thf('168',plain,(
    r1_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['165','167'])).

thf('169',plain,(
    r1_orders_2 @ sk_A @ sk_C @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['164','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['157','169'])).

thf('171',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','170'])).

thf('172',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('173',plain,(
    r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('175',plain,(
    r1_lattice3 @ sk_A @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    $false ),
    inference(demod,[status(thm)],['77','175'])).


%------------------------------------------------------------------------------
