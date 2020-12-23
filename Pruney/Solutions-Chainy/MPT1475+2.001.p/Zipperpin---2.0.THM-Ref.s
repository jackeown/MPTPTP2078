%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dxzaltc3Cy

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:23 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 520 expanded)
%              Number of leaves         :   19 ( 161 expanded)
%              Depth                    :   26
%              Number of atoms          : 1372 (6641 expanded)
%              Number of equality atoms :   76 ( 277 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) )
        & ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_orders_2 @ ( g1_orders_2 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ~ ( v1_orders_2 @ X6 )
      | ( X6
        = ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_orders_2 @ X12 @ X13 )
       != ( g1_orders_2 @ X10 @ X11 ) )
      | ( X13 = X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) )
      | ( ( u1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( l1_orders_2 @ ( g1_orders_2 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(involutiveness_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ ( k3_relset_1 @ A @ B @ C ) )
        = C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_relset_1 @ X4 @ X5 @ ( k3_relset_1 @ X4 @ X5 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ~ ( v1_orders_2 @ X6 )
      | ( X6
        = ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_orders_2 @ X12 @ X13 )
       != ( g1_orders_2 @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X1 ) )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_relset_1 @ X4 @ X5 @ ( k3_relset_1 @ X4 @ X5 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ X0 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ X0 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_relset_1 @ X4 @ X5 @ ( k3_relset_1 @ X4 @ X5 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('82',plain,(
    ! [X6: $i] :
      ( ~ ( v1_orders_2 @ X6 )
      | ( X6
        = ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf(t8_lattice3,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ ( k7_lattice3 @ A ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( k7_lattice3 @ ( k7_lattice3 @ A ) )
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_lattice3])).

thf('93',plain,(
    ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
 != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
     != ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
 != ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(simplify,[status(thm)],['96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dxzaltc3Cy
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.09  % Solved by: fo/fo7.sh
% 2.82/3.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.09  % done 1146 iterations in 2.610s
% 2.82/3.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.09  % SZS output start Refutation
% 2.82/3.09  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 2.82/3.09  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 2.82/3.09  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 2.82/3.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.82/3.09  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.82/3.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.82/3.09  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 2.82/3.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.82/3.09  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.09  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 2.82/3.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.82/3.09  thf(d5_lattice3, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( l1_orders_2 @ A ) =>
% 2.82/3.09       ( ( k7_lattice3 @ A ) =
% 2.82/3.09         ( g1_orders_2 @
% 2.82/3.09           ( u1_struct_0 @ A ) @ 
% 2.82/3.09           ( k3_relset_1 @
% 2.82/3.09             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 2.82/3.09  thf('0', plain,
% 2.82/3.09      (![X14 : $i]:
% 2.82/3.09         (((k7_lattice3 @ X14)
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09                (u1_orders_2 @ X14))))
% 2.82/3.09          | ~ (l1_orders_2 @ X14))),
% 2.82/3.09      inference('cnf', [status(esa)], [d5_lattice3])).
% 2.82/3.09  thf(dt_u1_orders_2, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( l1_orders_2 @ A ) =>
% 2.82/3.09       ( m1_subset_1 @
% 2.82/3.09         ( u1_orders_2 @ A ) @ 
% 2.82/3.09         ( k1_zfmisc_1 @
% 2.82/3.09           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 2.82/3.09  thf('1', plain,
% 2.82/3.09      (![X9 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 2.82/3.09          | ~ (l1_orders_2 @ X9))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 2.82/3.09  thf(dt_k3_relset_1, axiom,
% 2.82/3.09    (![A:$i,B:$i,C:$i]:
% 2.82/3.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.09       ( m1_subset_1 @
% 2.82/3.09         ( k3_relset_1 @ A @ B @ C ) @ 
% 2.82/3.09         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 2.82/3.09  thf('2', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (k3_relset_1 @ X0 @ X1 @ X2) @ 
% 2.82/3.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.82/3.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 2.82/3.09  thf('3', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ 
% 2.82/3.09             (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_orders_2 @ X0)) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['1', '2'])).
% 2.82/3.09  thf(dt_g1_orders_2, axiom,
% 2.82/3.09    (![A:$i,B:$i]:
% 2.82/3.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 2.82/3.09       ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) ) & 
% 2.82/3.09         ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ))).
% 2.82/3.09  thf('4', plain,
% 2.82/3.09      (![X7 : $i, X8 : $i]:
% 2.82/3.09         ((v1_orders_2 @ (g1_orders_2 @ X7 @ X8))
% 2.82/3.09          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 2.82/3.09  thf('5', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (v1_orders_2 @ 
% 2.82/3.09             (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['3', '4'])).
% 2.82/3.09  thf(abstractness_v1_orders_2, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( l1_orders_2 @ A ) =>
% 2.82/3.09       ( ( v1_orders_2 @ A ) =>
% 2.82/3.09         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 2.82/3.09  thf('6', plain,
% 2.82/3.09      (![X6 : $i]:
% 2.82/3.09         (~ (v1_orders_2 @ X6)
% 2.82/3.09          | ((X6) = (g1_orders_2 @ (u1_struct_0 @ X6) @ (u1_orders_2 @ X6)))
% 2.82/3.09          | ~ (l1_orders_2 @ X6))),
% 2.82/3.09      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 2.82/3.09  thf('7', plain,
% 2.82/3.09      (![X9 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 2.82/3.09          | ~ (l1_orders_2 @ X9))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 2.82/3.09  thf(free_g1_orders_2, axiom,
% 2.82/3.09    (![A:$i,B:$i]:
% 2.82/3.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 2.82/3.09       ( ![C:$i,D:$i]:
% 2.82/3.09         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 2.82/3.09           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 2.82/3.09  thf('8', plain,
% 2.82/3.09      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.82/3.09         (((g1_orders_2 @ X12 @ X13) != (g1_orders_2 @ X10 @ X11))
% 2.82/3.09          | ((X13) = (X11))
% 2.82/3.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12))))),
% 2.82/3.09      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 2.82/3.09  thf('9', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_orders_2 @ X0) = (X1))
% 2.82/3.09          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 2.82/3.09              != (g1_orders_2 @ X2 @ X1)))),
% 2.82/3.09      inference('sup-', [status(thm)], ['7', '8'])).
% 2.82/3.09  thf('10', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.09         (((X0) != (g1_orders_2 @ X2 @ X1))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (v1_orders_2 @ X0)
% 2.82/3.09          | ((u1_orders_2 @ X0) = (X1))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup-', [status(thm)], ['6', '9'])).
% 2.82/3.09  thf('11', plain,
% 2.82/3.09      (![X1 : $i, X2 : $i]:
% 2.82/3.09         (((u1_orders_2 @ (g1_orders_2 @ X2 @ X1)) = (X1))
% 2.82/3.09          | ~ (v1_orders_2 @ (g1_orders_2 @ X2 @ X1))
% 2.82/3.09          | ~ (l1_orders_2 @ (g1_orders_2 @ X2 @ X1)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['10'])).
% 2.82/3.09  thf('12', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ 
% 2.82/3.09               (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ X0))))
% 2.82/3.09          | ((u1_orders_2 @ 
% 2.82/3.09              (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                (u1_orders_2 @ X0))))
% 2.82/3.09              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ X0))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['5', '11'])).
% 2.82/3.09  thf('13', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ 
% 2.82/3.09             (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_orders_2 @ X0)) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['1', '2'])).
% 2.82/3.09  thf('14', plain,
% 2.82/3.09      (![X7 : $i, X8 : $i]:
% 2.82/3.09         ((l1_orders_2 @ (g1_orders_2 @ X7 @ X8))
% 2.82/3.09          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 2.82/3.09  thf('15', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (l1_orders_2 @ 
% 2.82/3.09             (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['13', '14'])).
% 2.82/3.09  thf('16', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_orders_2 @ 
% 2.82/3.09            (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09             (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_orders_2 @ X0))))
% 2.82/3.09            = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('clc', [status(thm)], ['12', '15'])).
% 2.82/3.09  thf('17', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09            = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['0', '16'])).
% 2.82/3.09  thf('18', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ X0))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['17'])).
% 2.82/3.09  thf('19', plain,
% 2.82/3.09      (![X9 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 2.82/3.09          | ~ (l1_orders_2 @ X9))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 2.82/3.09  thf(involutiveness_k3_relset_1, axiom,
% 2.82/3.09    (![A:$i,B:$i,C:$i]:
% 2.82/3.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.09       ( ( k3_relset_1 @ A @ B @ ( k3_relset_1 @ A @ B @ C ) ) = ( C ) ) ))).
% 2.82/3.09  thf('20', plain,
% 2.82/3.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.82/3.09         (((k3_relset_1 @ X4 @ X5 @ (k3_relset_1 @ X4 @ X5 @ X3)) = (X3))
% 2.82/3.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.82/3.09      inference('cnf', [status(esa)], [involutiveness_k3_relset_1])).
% 2.82/3.09  thf('21', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))
% 2.82/3.09              = (u1_orders_2 @ X0)))),
% 2.82/3.09      inference('sup-', [status(thm)], ['19', '20'])).
% 2.82/3.09  thf('22', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09            (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['18', '21'])).
% 2.82/3.09  thf('23', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['22'])).
% 2.82/3.09  thf('24', plain,
% 2.82/3.09      (![X14 : $i]:
% 2.82/3.09         (((k7_lattice3 @ X14)
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09                (u1_orders_2 @ X14))))
% 2.82/3.09          | ~ (l1_orders_2 @ X14))),
% 2.82/3.09      inference('cnf', [status(esa)], [d5_lattice3])).
% 2.82/3.09  thf('25', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (l1_orders_2 @ 
% 2.82/3.09             (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['13', '14'])).
% 2.82/3.09  thf('26', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         ((l1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['24', '25'])).
% 2.82/3.09  thf('27', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['26'])).
% 2.82/3.09  thf('28', plain,
% 2.82/3.09      (![X14 : $i]:
% 2.82/3.09         (((k7_lattice3 @ X14)
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09                (u1_orders_2 @ X14))))
% 2.82/3.09          | ~ (l1_orders_2 @ X14))),
% 2.82/3.09      inference('cnf', [status(esa)], [d5_lattice3])).
% 2.82/3.09  thf('29', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (v1_orders_2 @ 
% 2.82/3.09             (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['3', '4'])).
% 2.82/3.09  thf('30', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         ((v1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['28', '29'])).
% 2.82/3.09  thf('31', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['30'])).
% 2.82/3.09  thf('32', plain,
% 2.82/3.09      (![X6 : $i]:
% 2.82/3.09         (~ (v1_orders_2 @ X6)
% 2.82/3.09          | ((X6) = (g1_orders_2 @ (u1_struct_0 @ X6) @ (u1_orders_2 @ X6)))
% 2.82/3.09          | ~ (l1_orders_2 @ X6))),
% 2.82/3.09      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 2.82/3.09  thf('33', plain,
% 2.82/3.09      (![X14 : $i]:
% 2.82/3.09         (((k7_lattice3 @ X14)
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09                (u1_orders_2 @ X14))))
% 2.82/3.09          | ~ (l1_orders_2 @ X14))),
% 2.82/3.09      inference('cnf', [status(esa)], [d5_lattice3])).
% 2.82/3.09  thf('34', plain,
% 2.82/3.09      (![X9 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 2.82/3.09          | ~ (l1_orders_2 @ X9))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 2.82/3.09  thf('35', plain,
% 2.82/3.09      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.82/3.09         (((g1_orders_2 @ X12 @ X13) != (g1_orders_2 @ X10 @ X11))
% 2.82/3.09          | ((X12) = (X10))
% 2.82/3.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12))))),
% 2.82/3.09      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 2.82/3.09  thf('36', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_struct_0 @ X0) = (X1))
% 2.82/3.09          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 2.82/3.09              != (g1_orders_2 @ X1 @ X2)))),
% 2.82/3.09      inference('sup-', [status(thm)], ['34', '35'])).
% 2.82/3.09  thf('37', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i]:
% 2.82/3.09         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 2.82/3.09            != (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_struct_0 @ X1) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X1))),
% 2.82/3.09      inference('sup-', [status(thm)], ['33', '36'])).
% 2.82/3.09  thf('38', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i]:
% 2.82/3.09         (((X0) != (k7_lattice3 @ X1))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (v1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_struct_0 @ X0) = (u1_struct_0 @ X1))
% 2.82/3.09          | ~ (l1_orders_2 @ X1))),
% 2.82/3.09      inference('sup-', [status(thm)], ['32', '37'])).
% 2.82/3.09  thf('39', plain,
% 2.82/3.09      (![X1 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X1)
% 2.82/3.09          | ((u1_struct_0 @ (k7_lattice3 @ X1)) = (u1_struct_0 @ X1))
% 2.82/3.09          | ~ (v1_orders_2 @ (k7_lattice3 @ X1))
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X1)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['38'])).
% 2.82/3.09  thf('40', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup-', [status(thm)], ['31', '39'])).
% 2.82/3.09  thf('41', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['40'])).
% 2.82/3.09  thf('42', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0)))),
% 2.82/3.09      inference('sup-', [status(thm)], ['27', '41'])).
% 2.82/3.09  thf('43', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('44', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('45', plain,
% 2.82/3.09      (![X9 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 2.82/3.09          | ~ (l1_orders_2 @ X9))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 2.82/3.09  thf('46', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09             (u1_struct_0 @ (k7_lattice3 @ X0)))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('sup+', [status(thm)], ['44', '45'])).
% 2.82/3.09  thf('47', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['26'])).
% 2.82/3.09  thf('48', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ (u1_orders_2 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0))))))),
% 2.82/3.09      inference('clc', [status(thm)], ['46', '47'])).
% 2.82/3.09  thf('49', plain,
% 2.82/3.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.82/3.09         (((k3_relset_1 @ X4 @ X5 @ (k3_relset_1 @ X4 @ X5 @ X3)) = (X3))
% 2.82/3.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.82/3.09      inference('cnf', [status(esa)], [involutiveness_k3_relset_1])).
% 2.82/3.09  thf('50', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09               (u1_orders_2 @ (k7_lattice3 @ X0))))
% 2.82/3.09              = (u1_orders_2 @ (k7_lattice3 @ X0))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['48', '49'])).
% 2.82/3.09  thf('51', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09            (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09            (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09             (u1_orders_2 @ (k7_lattice3 @ X0))))
% 2.82/3.09            = (u1_orders_2 @ (k7_lattice3 @ X0)))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['43', '50'])).
% 2.82/3.09  thf('52', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ (k7_lattice3 @ X0))))
% 2.82/3.09              = (u1_orders_2 @ (k7_lattice3 @ X0))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['51'])).
% 2.82/3.09  thf('53', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09            (u1_struct_0 @ (k7_lattice3 @ X0)) @ (u1_orders_2 @ X0))
% 2.82/3.09            = (u1_orders_2 @ (k7_lattice3 @ X0)))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['23', '52'])).
% 2.82/3.09  thf('54', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_struct_0 @ (k7_lattice3 @ X0)) @ (u1_orders_2 @ X0))
% 2.82/3.09              = (u1_orders_2 @ (k7_lattice3 @ X0))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['53'])).
% 2.82/3.09  thf('55', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['22'])).
% 2.82/3.09  thf('56', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('57', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('58', plain,
% 2.82/3.09      (![X9 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 2.82/3.09          | ~ (l1_orders_2 @ X9))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 2.82/3.09  thf('59', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09             (u1_struct_0 @ X0))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('sup+', [status(thm)], ['57', '58'])).
% 2.82/3.09  thf('60', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['26'])).
% 2.82/3.09  thf('61', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ (u1_orders_2 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09               (u1_struct_0 @ X0)))))),
% 2.82/3.09      inference('clc', [status(thm)], ['59', '60'])).
% 2.82/3.09  thf('62', plain,
% 2.82/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (k3_relset_1 @ X0 @ X1 @ X2) @ 
% 2.82/3.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.82/3.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 2.82/3.09  thf('63', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ 
% 2.82/3.09             (k3_relset_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09              (u1_struct_0 @ X0) @ (u1_orders_2 @ (k7_lattice3 @ X0))) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0))))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['61', '62'])).
% 2.82/3.09  thf('64', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         ((m1_subset_1 @ 
% 2.82/3.09           (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09            (u1_orders_2 @ (k7_lattice3 @ X0))) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09             (u1_struct_0 @ (k7_lattice3 @ X0)))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['56', '63'])).
% 2.82/3.09  thf('65', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ 
% 2.82/3.09             (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_orders_2 @ (k7_lattice3 @ X0))) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0))))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['64'])).
% 2.82/3.09  thf('66', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09             (u1_struct_0 @ (k7_lattice3 @ X0)))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['55', '65'])).
% 2.82/3.09  thf('67', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | (m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0))))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['66'])).
% 2.82/3.09  thf('68', plain,
% 2.82/3.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.82/3.09         (((k3_relset_1 @ X4 @ X5 @ (k3_relset_1 @ X4 @ X5 @ X3)) = (X3))
% 2.82/3.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.82/3.09      inference('cnf', [status(esa)], [involutiveness_k3_relset_1])).
% 2.82/3.09  thf('69', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09              (k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0)) @ (u1_orders_2 @ X0)))
% 2.82/3.09              = (u1_orders_2 @ X0)))),
% 2.82/3.09      inference('sup-', [status(thm)], ['67', '68'])).
% 2.82/3.09  thf('70', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09            (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09            (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['54', '69'])).
% 2.82/3.09  thf('71', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09              (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09              (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['70'])).
% 2.82/3.09  thf('72', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('73', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ X0))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['17'])).
% 2.82/3.09  thf('74', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_orders_2 @ (k7_lattice3 @ (k7_lattice3 @ X0)))
% 2.82/3.09            = (k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09               (u1_orders_2 @ (k7_lattice3 @ X0))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('sup+', [status(thm)], ['72', '73'])).
% 2.82/3.09  thf('75', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['26'])).
% 2.82/3.09  thf('76', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_orders_2 @ (k7_lattice3 @ (k7_lattice3 @ X0)))
% 2.82/3.09              = (k3_relset_1 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 2.82/3.09                 (u1_orders_2 @ (k7_lattice3 @ X0)))))),
% 2.82/3.09      inference('clc', [status(thm)], ['74', '75'])).
% 2.82/3.09  thf('77', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_orders_2 @ (k7_lattice3 @ (k7_lattice3 @ X0)))
% 2.82/3.09            = (u1_orders_2 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['71', '76'])).
% 2.82/3.09  thf('78', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((u1_orders_2 @ (k7_lattice3 @ (k7_lattice3 @ X0)))
% 2.82/3.09              = (u1_orders_2 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['77'])).
% 2.82/3.09  thf('79', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('80', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['26'])).
% 2.82/3.09  thf('81', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['42'])).
% 2.82/3.09  thf('82', plain,
% 2.82/3.09      (![X6 : $i]:
% 2.82/3.09         (~ (v1_orders_2 @ X6)
% 2.82/3.09          | ((X6) = (g1_orders_2 @ (u1_struct_0 @ X6) @ (u1_orders_2 @ X6)))
% 2.82/3.09          | ~ (l1_orders_2 @ X6))),
% 2.82/3.09      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 2.82/3.09  thf('83', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k7_lattice3 @ X0)
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ (k7_lattice3 @ X0))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (v1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('sup+', [status(thm)], ['81', '82'])).
% 2.82/3.09  thf('84', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (v1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k7_lattice3 @ X0)
% 2.82/3.09              = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ (k7_lattice3 @ X0)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['80', '83'])).
% 2.82/3.09  thf('85', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k7_lattice3 @ X0)
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ (k7_lattice3 @ X0))))
% 2.82/3.09          | ~ (v1_orders_2 @ (k7_lattice3 @ X0))
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('simplify', [status(thm)], ['84'])).
% 2.82/3.09  thf('86', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['30'])).
% 2.82/3.09  thf('87', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k7_lattice3 @ X0)
% 2.82/3.09              = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ (k7_lattice3 @ X0)))))),
% 2.82/3.09      inference('clc', [status(thm)], ['85', '86'])).
% 2.82/3.09  thf('88', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09               (u1_orders_2 @ (k7_lattice3 @ (k7_lattice3 @ X0)))))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('sup+', [status(thm)], ['79', '87'])).
% 2.82/3.09  thf('89', plain,
% 2.82/3.09      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 2.82/3.09      inference('simplify', [status(thm)], ['26'])).
% 2.82/3.09  thf('90', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 2.82/3.09              = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 2.82/3.09                 (u1_orders_2 @ (k7_lattice3 @ (k7_lattice3 @ X0))))))),
% 2.82/3.09      inference('clc', [status(thm)], ['88', '89'])).
% 2.82/3.09  thf('91', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 2.82/3.09            = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 2.82/3.09          | ~ (l1_orders_2 @ X0)
% 2.82/3.09          | ~ (l1_orders_2 @ X0))),
% 2.82/3.09      inference('sup+', [status(thm)], ['78', '90'])).
% 2.82/3.09  thf('92', plain,
% 2.82/3.09      (![X0 : $i]:
% 2.82/3.09         (~ (l1_orders_2 @ X0)
% 2.82/3.09          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 2.82/3.09              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))))),
% 2.82/3.09      inference('simplify', [status(thm)], ['91'])).
% 2.82/3.09  thf(t8_lattice3, conjecture,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( l1_orders_2 @ A ) =>
% 2.82/3.09       ( ( k7_lattice3 @ ( k7_lattice3 @ A ) ) =
% 2.82/3.09         ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ))).
% 2.82/3.09  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.09    (~( ![A:$i]:
% 2.82/3.09        ( ( l1_orders_2 @ A ) =>
% 2.82/3.09          ( ( k7_lattice3 @ ( k7_lattice3 @ A ) ) =
% 2.82/3.09            ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) )),
% 2.82/3.09    inference('cnf.neg', [status(esa)], [t8_lattice3])).
% 2.82/3.09  thf('93', plain,
% 2.82/3.09      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 2.82/3.09         != (g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A)))),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('94', plain,
% 2.82/3.09      ((((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 2.82/3.09          != (k7_lattice3 @ (k7_lattice3 @ sk_A)))
% 2.82/3.09        | ~ (l1_orders_2 @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['92', '93'])).
% 2.82/3.09  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('96', plain,
% 2.82/3.09      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 2.82/3.09         != (k7_lattice3 @ (k7_lattice3 @ sk_A)))),
% 2.82/3.09      inference('demod', [status(thm)], ['94', '95'])).
% 2.82/3.09  thf('97', plain, ($false), inference('simplify', [status(thm)], ['96'])).
% 2.82/3.09  
% 2.82/3.09  % SZS output end Refutation
% 2.82/3.09  
% 2.92/3.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
