%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ciicaq6ZrH

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:41 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  228 (1130 expanded)
%              Number of leaves         :   33 ( 339 expanded)
%              Depth                    :   45
%              Number of atoms          : 2213 (14233 expanded)
%              Number of equality atoms :   87 ( 584 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k8_lattice3_type,type,(
    k8_lattice3: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t9_lattice3,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r1_orders_2 @ ( k7_lattice3 @ A ) @ ( k8_lattice3 @ A @ C ) @ ( k8_lattice3 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_orders_2 @ A @ B @ C )
                <=> ( r1_orders_2 @ ( k7_lattice3 @ A ) @ ( k8_lattice3 @ A @ C ) @ ( k8_lattice3 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_lattice3])).

thf('0',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('3',plain,(
    ! [X16: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_relset_1 @ X26 @ X27 @ X25 )
        = ( k4_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( ( k7_lattice3 @ X4 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X4 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_orders_2 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( g1_orders_2 @ X22 @ X23 )
       != ( g1_orders_2 @ X20 @ X21 ) )
      | ( X23 = X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X1 )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = ( k4_relat_1 @ ( u1_orders_2 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X1 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( ( k7_lattice3 @ X4 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X4 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_orders_2 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( g1_orders_2 @ X22 @ X23 )
       != ( g1_orders_2 @ X20 @ X21 ) )
      | ( X22 = X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X1 ) )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X16: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('44',plain,(
    ! [X24: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','57'])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) )
        = ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','64'])).

thf('66',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','67'])).

thf('69',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('83',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('85',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k8_lattice3 @ A @ B )
            = B ) ) ) )).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( ( k8_lattice3 @ X6 @ X5 )
        = X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_lattice3])).

thf('88',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_lattice3 @ sk_A @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( ( k8_lattice3 @ X6 @ X5 )
        = X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_lattice3])).

thf('93',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_lattice3 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['85','90','95'])).

thf('97',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['88','89'])).

thf('98',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('99',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('105',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('112',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X7
       != ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('113',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('121',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','121'])).

thf('123',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','122'])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('127',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','127'])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','130'])).

thf('132',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('135',plain,
    ( ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
      | ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k8_lattice3 @ A @ B ) @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('137',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k8_lattice3 @ X17 @ X18 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_lattice3])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k8_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('140',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k8_lattice3 @ X17 @ X18 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_lattice3])).

thf('144',plain,
    ( ( m1_subset_1 @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['88','89'])).

thf('146',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','141','147'])).

thf('149',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('150',plain,
    ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( l1_orders_2 @ sk_A )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','150'])).

thf('152',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ ( k7_lattice3 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('159',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
   <= ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['159'])).

thf('161',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['88','89'])).

thf('162',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('163',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['153'])).

thf('165',plain,(
    r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X16: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('167',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('168',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('175',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['158','175'])).

thf('177',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X7
       != ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('180',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','180'])).

thf('182',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','183'])).

thf('185',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('188',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    $false ),
    inference(demod,[status(thm)],['156','192'])).


%------------------------------------------------------------------------------
