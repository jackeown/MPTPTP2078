%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1476+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QTa443GSd8

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:41 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 902 expanded)
%              Number of leaves         :   34 ( 271 expanded)
%              Depth                    :   43
%              Number of atoms          : 2281 (12012 expanded)
%              Number of equality atoms :   62 ( 258 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('3',plain,(
    ! [X20: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
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
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k3_relset_1 @ X33 @ X34 @ X32 )
        = ( k4_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( ( g1_orders_2 @ X26 @ X27 )
       != ( g1_orders_2 @ X24 @ X25 ) )
      | ( X27 = X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_lattice3 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ( ( k4_relat_1 @ ( u1_orders_2 @ X1 ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( ( k4_relat_1 @ ( u1_orders_2 @ X1 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('29',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k3_relset_1 @ X33 @ X34 @ X32 )
        = ( k4_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
        = ( k4_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(involutiveness_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ ( k3_relset_1 @ A @ B @ C ) )
        = C ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k3_relset_1 @ X29 @ X30 @ ( k3_relset_1 @ X29 @ X30 @ X28 ) )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('48',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k3_relset_1 @ X33 @ X34 @ X32 )
        = ( k4_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
        = ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('65',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k8_lattice3 @ A @ B )
            = B ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( ( k8_lattice3 @ X6 @ X5 )
        = X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_lattice3])).

thf('68',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_lattice3 @ sk_A @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( ( k8_lattice3 @ X6 @ X5 )
        = X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_lattice3])).

thf('73',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( k8_lattice3 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','70','75'])).

thf('77',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('78',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('79',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

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

thf('92',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X7
       != ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('93',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('101',plain,(
    ! [X31: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X31 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('102',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('113',plain,
    ( ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','113'])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','119'])).

thf('121',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('124',plain,
    ( ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
      | ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k8_lattice3 @ A @ B ) @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('126',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k8_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_lattice3])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k8_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k8_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k7_lattice3 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_lattice3])).

thf('133',plain,
    ( ( m1_subset_1 @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('135',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','130','136'])).

thf('138',plain,
    ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('139',plain,
    ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( l1_orders_2 @ sk_A )
   <= ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','139'])).

thf('141',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('144',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k4_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('149',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) )
   <= ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['149'])).

thf('151',plain,
    ( ( k8_lattice3 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('152',plain,
    ( ( k8_lattice3 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('153',plain,
    ( ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ ( k8_lattice3 @ sk_A @ sk_C_1 ) @ ( k8_lattice3 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['142'])).

thf('155',plain,(
    r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('157',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('158',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k7_lattice3 @ sk_A ) @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['155','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('165',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['148','165'])).

thf('167',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X7
       != ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('170',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k4_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','170'])).

thf('172',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','171'])).

thf('173',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','174'])).

thf('176',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('179',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['145','183'])).


%------------------------------------------------------------------------------
