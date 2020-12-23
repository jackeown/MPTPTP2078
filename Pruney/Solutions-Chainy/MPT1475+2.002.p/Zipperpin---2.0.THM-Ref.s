%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JI8u3v2CZJ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:23 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 115 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  721 (1301 expanded)
%              Number of equality atoms :   54 (  98 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(dt_k7_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ~ ( v1_orders_2 @ X3 )
      | ( X3
        = ( g1_orders_2 @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k7_lattice3 @ X9 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X1 )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = ( k3_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X1 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(involutiveness_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ ( k3_relset_1 @ A @ B @ C ) )
        = C ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_relset_1 @ X1 @ X2 @ ( k3_relset_1 @ X1 @ X2 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('19',plain,(
    ! [X3: $i] :
      ( ~ ( v1_orders_2 @ X3 )
      | ( X3
        = ( g1_orders_2 @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('20',plain,(
    ! [X9: $i] :
      ( ( ( k7_lattice3 @ X9 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X1 ) )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( ( k7_lattice3 @ X9 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X9 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) @ ( u1_orders_2 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( k3_relset_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( k3_relset_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

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

thf('43',plain,(
    ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
 != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
     != ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
 != ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JI8u3v2CZJ
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.89  % Solved by: fo/fo7.sh
% 0.65/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.89  % done 237 iterations in 0.411s
% 0.65/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.89  % SZS output start Refutation
% 0.65/0.89  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.65/0.89  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.65/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.89  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.65/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.65/0.89  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.65/0.89  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.65/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.89  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.65/0.89  thf(dt_k7_lattice3, axiom,
% 0.65/0.89    (![A:$i]:
% 0.65/0.89     ( ( l1_orders_2 @ A ) =>
% 0.65/0.89       ( ( v1_orders_2 @ ( k7_lattice3 @ A ) ) & 
% 0.65/0.89         ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.65/0.89  thf('0', plain,
% 0.65/0.89      (![X10 : $i]:
% 0.65/0.89         ((v1_orders_2 @ (k7_lattice3 @ X10)) | ~ (l1_orders_2 @ X10))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.65/0.89  thf(abstractness_v1_orders_2, axiom,
% 0.65/0.89    (![A:$i]:
% 0.65/0.89     ( ( l1_orders_2 @ A ) =>
% 0.65/0.89       ( ( v1_orders_2 @ A ) =>
% 0.65/0.89         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.65/0.89  thf('1', plain,
% 0.65/0.89      (![X3 : $i]:
% 0.65/0.89         (~ (v1_orders_2 @ X3)
% 0.65/0.89          | ((X3) = (g1_orders_2 @ (u1_struct_0 @ X3) @ (u1_orders_2 @ X3)))
% 0.65/0.89          | ~ (l1_orders_2 @ X3))),
% 0.65/0.89      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.65/0.89  thf(d5_lattice3, axiom,
% 0.65/0.89    (![A:$i]:
% 0.65/0.89     ( ( l1_orders_2 @ A ) =>
% 0.65/0.89       ( ( k7_lattice3 @ A ) =
% 0.65/0.89         ( g1_orders_2 @
% 0.65/0.89           ( u1_struct_0 @ A ) @ 
% 0.65/0.89           ( k3_relset_1 @
% 0.65/0.89             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.65/0.89  thf('2', plain,
% 0.65/0.89      (![X9 : $i]:
% 0.65/0.89         (((k7_lattice3 @ X9)
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ X9) @ 
% 0.65/0.89               (k3_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9) @ 
% 0.65/0.89                (u1_orders_2 @ X9))))
% 0.65/0.89          | ~ (l1_orders_2 @ X9))),
% 0.65/0.89      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.65/0.89  thf(dt_u1_orders_2, axiom,
% 0.65/0.89    (![A:$i]:
% 0.65/0.89     ( ( l1_orders_2 @ A ) =>
% 0.65/0.89       ( m1_subset_1 @
% 0.65/0.89         ( u1_orders_2 @ A ) @ 
% 0.65/0.89         ( k1_zfmisc_1 @
% 0.65/0.89           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.65/0.89  thf('3', plain,
% 0.65/0.89      (![X4 : $i]:
% 0.65/0.89         ((m1_subset_1 @ (u1_orders_2 @ X4) @ 
% 0.65/0.89           (k1_zfmisc_1 @ 
% 0.65/0.89            (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4))))
% 0.65/0.89          | ~ (l1_orders_2 @ X4))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.65/0.89  thf(free_g1_orders_2, axiom,
% 0.65/0.89    (![A:$i,B:$i]:
% 0.65/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.65/0.89       ( ![C:$i,D:$i]:
% 0.65/0.89         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.65/0.89           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.65/0.89  thf('4', plain,
% 0.65/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.89         (((g1_orders_2 @ X7 @ X8) != (g1_orders_2 @ X5 @ X6))
% 0.65/0.89          | ((X8) = (X6))
% 0.65/0.89          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 0.65/0.89      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.65/0.89  thf('5', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_orders_2 @ X0) = (X1))
% 0.65/0.89          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.65/0.89              != (g1_orders_2 @ X2 @ X1)))),
% 0.65/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.65/0.89  thf('6', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i]:
% 0.65/0.89         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 0.65/0.89            != (k7_lattice3 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_orders_2 @ X1)
% 0.65/0.89              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                 (u1_orders_2 @ X0)))
% 0.65/0.89          | ~ (l1_orders_2 @ X1))),
% 0.65/0.89      inference('sup-', [status(thm)], ['2', '5'])).
% 0.65/0.89  thf('7', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i]:
% 0.65/0.89         (((X0) != (k7_lattice3 @ X1))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (v1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_orders_2 @ X0)
% 0.65/0.89              = (k3_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X1) @ 
% 0.65/0.89                 (u1_orders_2 @ X1)))
% 0.65/0.89          | ~ (l1_orders_2 @ X1))),
% 0.65/0.89      inference('sup-', [status(thm)], ['1', '6'])).
% 0.65/0.89  thf('8', plain,
% 0.65/0.89      (![X1 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X1)
% 0.65/0.89          | ((u1_orders_2 @ (k7_lattice3 @ X1))
% 0.65/0.89              = (k3_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X1) @ 
% 0.65/0.89                 (u1_orders_2 @ X1)))
% 0.65/0.89          | ~ (v1_orders_2 @ (k7_lattice3 @ X1))
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X1)))),
% 0.65/0.89      inference('simplify', [status(thm)], ['7'])).
% 0.65/0.89  thf('9', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89          | ((u1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                 (u1_orders_2 @ X0)))
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('sup-', [status(thm)], ['0', '8'])).
% 0.65/0.89  thf('10', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((u1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89            = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89               (u1_orders_2 @ X0)))
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('simplify', [status(thm)], ['9'])).
% 0.65/0.89  thf('11', plain,
% 0.65/0.89      (![X10 : $i]:
% 0.65/0.89         ((l1_orders_2 @ (k7_lattice3 @ X10)) | ~ (l1_orders_2 @ X10))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.65/0.89  thf('12', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89              = (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                 (u1_orders_2 @ X0))))),
% 0.65/0.89      inference('clc', [status(thm)], ['10', '11'])).
% 0.65/0.89  thf('13', plain,
% 0.65/0.89      (![X4 : $i]:
% 0.65/0.89         ((m1_subset_1 @ (u1_orders_2 @ X4) @ 
% 0.65/0.89           (k1_zfmisc_1 @ 
% 0.65/0.89            (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4))))
% 0.65/0.89          | ~ (l1_orders_2 @ X4))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.65/0.89  thf(involutiveness_k3_relset_1, axiom,
% 0.65/0.89    (![A:$i,B:$i,C:$i]:
% 0.65/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.89       ( ( k3_relset_1 @ A @ B @ ( k3_relset_1 @ A @ B @ C ) ) = ( C ) ) ))).
% 0.65/0.89  thf('14', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.89         (((k3_relset_1 @ X1 @ X2 @ (k3_relset_1 @ X1 @ X2 @ X0)) = (X0))
% 0.65/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.65/0.89      inference('cnf', [status(esa)], [involutiveness_k3_relset_1])).
% 0.65/0.89  thf('15', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89               (u1_orders_2 @ X0)))
% 0.65/0.89              = (u1_orders_2 @ X0)))),
% 0.65/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.65/0.89  thf('16', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89            (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('sup+', [status(thm)], ['12', '15'])).
% 0.65/0.89  thf('17', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89              (u1_orders_2 @ (k7_lattice3 @ X0))) = (u1_orders_2 @ X0)))),
% 0.65/0.89      inference('simplify', [status(thm)], ['16'])).
% 0.65/0.89  thf('18', plain,
% 0.65/0.89      (![X10 : $i]:
% 0.65/0.89         ((v1_orders_2 @ (k7_lattice3 @ X10)) | ~ (l1_orders_2 @ X10))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.65/0.89  thf('19', plain,
% 0.65/0.89      (![X3 : $i]:
% 0.65/0.89         (~ (v1_orders_2 @ X3)
% 0.65/0.89          | ((X3) = (g1_orders_2 @ (u1_struct_0 @ X3) @ (u1_orders_2 @ X3)))
% 0.65/0.89          | ~ (l1_orders_2 @ X3))),
% 0.65/0.89      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.65/0.89  thf('20', plain,
% 0.65/0.89      (![X9 : $i]:
% 0.65/0.89         (((k7_lattice3 @ X9)
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ X9) @ 
% 0.65/0.89               (k3_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9) @ 
% 0.65/0.89                (u1_orders_2 @ X9))))
% 0.65/0.89          | ~ (l1_orders_2 @ X9))),
% 0.65/0.89      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.65/0.89  thf('21', plain,
% 0.65/0.89      (![X4 : $i]:
% 0.65/0.89         ((m1_subset_1 @ (u1_orders_2 @ X4) @ 
% 0.65/0.89           (k1_zfmisc_1 @ 
% 0.65/0.89            (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4))))
% 0.65/0.89          | ~ (l1_orders_2 @ X4))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.65/0.89  thf('22', plain,
% 0.65/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.65/0.89         (((g1_orders_2 @ X7 @ X8) != (g1_orders_2 @ X5 @ X6))
% 0.65/0.89          | ((X7) = (X5))
% 0.65/0.89          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 0.65/0.89      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.65/0.89  thf('23', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_struct_0 @ X0) = (X1))
% 0.65/0.89          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.65/0.89              != (g1_orders_2 @ X1 @ X2)))),
% 0.65/0.89      inference('sup-', [status(thm)], ['21', '22'])).
% 0.65/0.89  thf('24', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i]:
% 0.65/0.89         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 0.65/0.89            != (k7_lattice3 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_struct_0 @ X1) = (u1_struct_0 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X1))),
% 0.65/0.89      inference('sup-', [status(thm)], ['20', '23'])).
% 0.65/0.89  thf('25', plain,
% 0.65/0.89      (![X0 : $i, X1 : $i]:
% 0.65/0.89         (((X0) != (k7_lattice3 @ X1))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (v1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_struct_0 @ X0) = (u1_struct_0 @ X1))
% 0.65/0.89          | ~ (l1_orders_2 @ X1))),
% 0.65/0.89      inference('sup-', [status(thm)], ['19', '24'])).
% 0.65/0.89  thf('26', plain,
% 0.65/0.89      (![X1 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X1)
% 0.65/0.89          | ((u1_struct_0 @ (k7_lattice3 @ X1)) = (u1_struct_0 @ X1))
% 0.65/0.89          | ~ (v1_orders_2 @ (k7_lattice3 @ X1))
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X1)))),
% 0.65/0.89      inference('simplify', [status(thm)], ['25'])).
% 0.65/0.89  thf('27', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('sup-', [status(thm)], ['18', '26'])).
% 0.65/0.89  thf('28', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('simplify', [status(thm)], ['27'])).
% 0.65/0.89  thf('29', plain,
% 0.65/0.89      (![X10 : $i]:
% 0.65/0.89         ((l1_orders_2 @ (k7_lattice3 @ X10)) | ~ (l1_orders_2 @ X10))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.65/0.89  thf('30', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0)))),
% 0.65/0.89      inference('clc', [status(thm)], ['28', '29'])).
% 0.65/0.89  thf('31', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0)))),
% 0.65/0.89      inference('clc', [status(thm)], ['28', '29'])).
% 0.65/0.89  thf('32', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0)))),
% 0.65/0.89      inference('clc', [status(thm)], ['28', '29'])).
% 0.65/0.89  thf('33', plain,
% 0.65/0.89      (![X9 : $i]:
% 0.65/0.89         (((k7_lattice3 @ X9)
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ X9) @ 
% 0.65/0.89               (k3_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9) @ 
% 0.65/0.89                (u1_orders_2 @ X9))))
% 0.65/0.89          | ~ (l1_orders_2 @ X9))),
% 0.65/0.89      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.65/0.89  thf('34', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 0.65/0.89               (k3_relset_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 0.65/0.89                (u1_struct_0 @ X0) @ (u1_orders_2 @ (k7_lattice3 @ X0)))))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 0.65/0.89      inference('sup+', [status(thm)], ['32', '33'])).
% 0.65/0.89  thf('35', plain,
% 0.65/0.89      (![X10 : $i]:
% 0.65/0.89         ((l1_orders_2 @ (k7_lattice3 @ X10)) | ~ (l1_orders_2 @ X10))),
% 0.65/0.89      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.65/0.89  thf('36', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89              = (g1_orders_2 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 0.65/0.89                 (k3_relset_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 0.65/0.89                  (u1_struct_0 @ X0) @ (u1_orders_2 @ (k7_lattice3 @ X0))))))),
% 0.65/0.89      inference('clc', [status(thm)], ['34', '35'])).
% 0.65/0.89  thf('37', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.65/0.89               (k3_relset_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 0.65/0.89                (u1_struct_0 @ X0) @ (u1_orders_2 @ (k7_lattice3 @ X0)))))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('sup+', [status(thm)], ['31', '36'])).
% 0.65/0.89  thf('38', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89              = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                 (k3_relset_1 @ (u1_struct_0 @ (k7_lattice3 @ X0)) @ 
% 0.65/0.89                  (u1_struct_0 @ X0) @ (u1_orders_2 @ (k7_lattice3 @ X0))))))),
% 0.65/0.89      inference('simplify', [status(thm)], ['37'])).
% 0.65/0.89  thf('39', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.65/0.89               (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                (u1_orders_2 @ (k7_lattice3 @ X0)))))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('sup+', [status(thm)], ['30', '38'])).
% 0.65/0.89  thf('40', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89              = (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                 (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.65/0.89                  (u1_orders_2 @ (k7_lattice3 @ X0))))))),
% 0.65/0.89      inference('simplify', [status(thm)], ['39'])).
% 0.65/0.89  thf('41', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89            = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.65/0.89          | ~ (l1_orders_2 @ X0)
% 0.65/0.89          | ~ (l1_orders_2 @ X0))),
% 0.65/0.89      inference('sup+', [status(thm)], ['17', '40'])).
% 0.65/0.89  thf('42', plain,
% 0.65/0.89      (![X0 : $i]:
% 0.65/0.89         (~ (l1_orders_2 @ X0)
% 0.65/0.89          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.65/0.89              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))))),
% 0.65/0.89      inference('simplify', [status(thm)], ['41'])).
% 0.65/0.89  thf(t8_lattice3, conjecture,
% 0.65/0.89    (![A:$i]:
% 0.65/0.89     ( ( l1_orders_2 @ A ) =>
% 0.65/0.89       ( ( k7_lattice3 @ ( k7_lattice3 @ A ) ) =
% 0.65/0.89         ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ))).
% 0.65/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.89    (~( ![A:$i]:
% 0.65/0.89        ( ( l1_orders_2 @ A ) =>
% 0.65/0.89          ( ( k7_lattice3 @ ( k7_lattice3 @ A ) ) =
% 0.65/0.89            ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) )),
% 0.65/0.89    inference('cnf.neg', [status(esa)], [t8_lattice3])).
% 0.65/0.89  thf('43', plain,
% 0.65/0.89      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.65/0.89         != (g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A)))),
% 0.65/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.89  thf('44', plain,
% 0.65/0.89      ((((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.65/0.89          != (k7_lattice3 @ (k7_lattice3 @ sk_A)))
% 0.65/0.89        | ~ (l1_orders_2 @ sk_A))),
% 0.65/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.65/0.89  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.89  thf('46', plain,
% 0.65/0.89      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.65/0.89         != (k7_lattice3 @ (k7_lattice3 @ sk_A)))),
% 0.65/0.89      inference('demod', [status(thm)], ['44', '45'])).
% 0.65/0.89  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.65/0.89  
% 0.65/0.89  % SZS output end Refutation
% 0.65/0.89  
% 0.73/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
