%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1440+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fv4et6NTGF

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:39 EST 2020

% Result     : Theorem 51.57s
% Output     : Refutation 51.60s
% Verified   : 
% Statistics : Number of formulae       :  861 (71154 expanded)
%              Number of leaves         :   52 (19887 expanded)
%              Depth                    :   85
%              Number of atoms          : 15378 (1666684 expanded)
%              Number of equality atoms :  245 (33140 expanded)
%              Maximal formula depth    :   29 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_binop_1_type,type,(
    v2_binop_1: $i > $i > $o )).

thf(u2_lattices_type,type,(
    u2_lattices: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_lattices_type,type,(
    u1_lattices: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_filter_1_type,type,(
    k7_filter_1: $i > $i > $i )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(g3_lattices_type,type,(
    g3_lattices: $i > $i > $i > $i )).

thf(v1_binop_1_type,type,(
    v1_binop_1: $i > $i > $o )).

thf(k6_filter_1_type,type,(
    k6_filter_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_lattice2_type,type,(
    r1_lattice2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(t35_filter_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l3_lattices @ B ) )
         => ( ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
              & ( v10_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) )
           => ( ~ ( v2_struct_0 @ A )
              & ( v10_lattices @ A )
              & ( l3_lattices @ A )
              & ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( l3_lattices @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l3_lattices @ B ) )
           => ( ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
                & ( v10_lattices @ ( k7_filter_1 @ A @ B ) )
                & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) )
             => ( ~ ( v2_struct_0 @ A )
                & ( v10_lattices @ A )
                & ( l3_lattices @ A )
                & ~ ( v2_struct_0 @ B )
                & ( v10_lattices @ B )
                & ( l3_lattices @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_filter_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_lattices,axiom,(
    ! [A: $i] :
      ( ( l1_lattices @ A )
     => ( ( v1_funct_1 @ ( u1_lattices @ A ) )
        & ( v1_funct_2 @ ( u1_lattices @ A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_lattices @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(fc7_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_lattices @ A )
        & ( l1_lattices @ A ) )
     => ( ( v1_funct_1 @ ( u1_lattices @ A ) )
        & ( v1_funct_2 @ ( u1_lattices @ A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) )
        & ( v2_binop_1 @ ( u1_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( v2_binop_1 @ ( u1_lattices @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_lattices @ X18 )
      | ~ ( v7_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_lattice2])).

thf('4',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) )
        & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_u2_lattices,axiom,(
    ! [A: $i] :
      ( ( l2_lattices @ A )
     => ( ( v1_funct_1 @ ( u2_lattices @ A ) )
        & ( v1_funct_2 @ ( u2_lattices @ A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u2_lattices @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('11',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(abstractness_v3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( v3_lattices @ A )
       => ( A
          = ( g3_lattices @ ( u1_struct_0 @ A ) @ ( u2_lattices @ A ) @ ( u1_lattices @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v3_lattices @ X0 )
      | ( X0
        = ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v3_lattices])).

thf(d7_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l3_lattices @ B ) )
         => ( ( k7_filter_1 @ A @ B )
            = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u2_lattices @ A ) @ ( u2_lattices @ B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_lattices @ A ) @ ( u1_lattices @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( ( k7_filter_1 @ X3 @ X2 )
        = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u2_lattices @ X3 ) @ ( u2_lattices @ X2 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u1_lattices @ X3 ) @ ( u1_lattices @ X2 ) ) ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_filter_1])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf(free_g3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
     => ! [D: $i,E: $i,F: $i] :
          ( ( ( g3_lattices @ A @ B @ C )
            = ( g3_lattices @ D @ E @ F ) )
         => ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ( X21 = X24 )
      | ( ( g3_lattices @ X20 @ X19 @ X21 )
       != ( g3_lattices @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[free_g3_lattices])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ X1 )
       != ( g3_lattices @ X4 @ X3 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_lattices @ X0 )
        = X1 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ( ( u1_lattices @ X0 )
        = X1 )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_lattices @ X0 )
        = X1 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ( ( u1_lattices @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( ( u1_lattices @ X0 )
        = X1 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g3_lattices @ ( u1_struct_0 @ X2 ) @ ( u2_lattices @ X2 ) @ ( u1_lattices @ X2 ) )
       != ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X2 )
      | ~ ( l2_lattices @ X2 )
      | ( ( u1_lattices @ X2 )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X2 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k7_filter_1 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v3_lattices @ X0 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( ( u1_lattices @ X0 )
        = ( k6_filter_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X1 ) @ ( u1_lattices @ X2 ) @ ( u1_lattices @ X1 ) ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X2 @ X1 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X2 @ X1 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X1 ) @ ( u1_lattices @ X2 ) @ ( u1_lattices @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ ( k7_filter_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ X2 @ X1 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ sk_B ) ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','35'])).

thf('37',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('40',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('43',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','40','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('50',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(t24_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ B @ B ) @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                 => ( ( ( v2_binop_1 @ C @ A )
                      & ( v2_binop_1 @ D @ B ) )
                  <=> ( v2_binop_1 @ ( k6_filter_1 @ A @ B @ C @ D ) @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 ) ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X32 @ X30 @ X33 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X30 ) )
      | ( v2_binop_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_filter_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ ( u1_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_binop_1 @ ( u1_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ ( u1_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v2_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('57',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('58',plain,
    ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( ( k7_filter_1 @ X3 @ X2 )
        = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u2_lattices @ X3 ) @ ( u2_lattices @ X2 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u1_lattices @ X3 ) @ ( u1_lattices @ X2 ) ) ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_filter_1])).

thf('60',plain,
    ( ( ( k7_filter_1 @ sk_A @ sk_B )
      = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k7_filter_1 @ sk_A @ sk_B )
      = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k7_filter_1 @ sk_A @ sk_B )
      = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v3_lattices @ X0 )
      | ( X0
        = ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v3_lattices])).

thf('69',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('70',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('71',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('72',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ( X20 = X22 )
      | ( ( g3_lattices @ X20 @ X19 @ X21 )
       != ( g3_lattices @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[free_g3_lattices])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ X1 )
       != ( g3_lattices @ X4 @ X3 @ X2 ) )
      | ( ( u1_struct_0 @ X0 )
        = X4 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X1 @ X3 @ X2 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ( ( u1_struct_0 @ X0 )
        = X3 )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = X3 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ( ( u1_struct_0 @ X0 )
        = X3 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = X3 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X3 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ ( u2_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) ) )
      | ( ( u1_struct_0 @ ( g3_lattices @ X3 @ X2 @ X1 ) )
        = X3 )
      | ~ ( l2_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l1_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( v3_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l3_lattices @ ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_lattices @ ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_lattices @ ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l2_lattices @ ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ( ( u1_struct_0 @ ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('84',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('86',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('87',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('88',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('89',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('90',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('91',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('92',plain,
    ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('93',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('94',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('95',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('96',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('97',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('98',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(dt_k6_filter_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ B @ B ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k6_filter_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k6_filter_1 @ A @ B @ C @ D ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) ) @ ( k2_zfmisc_1 @ A @ B ) )
        & ( m1_subset_1 @ ( k6_filter_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) ) @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('99',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X5 @ X5 ) @ X5 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( v1_funct_1 @ ( k6_filter_1 @ X5 @ X7 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_filter_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X2 ) @ X2 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X2 @ X2 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X2 @ X2 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X2 ) @ X2 ) ) )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X2 ) @ X2 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ X2 @ X2 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X1 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( l1_lattices @ X1 )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X1 ) ) )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l1_lattices @ X0 )
      | ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v1_funct_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_B )
    | ~ ( l1_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['92','109'])).

thf('111',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('113',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('116',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','113','116'])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( v3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88','89','90','91','117'])).

thf('119',plain,
    ( ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','118'])).

thf('120',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('121',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','121'])).

thf('123',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('128',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( l3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('129',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( l3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('132',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( l3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('135',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_A ) )
      | ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('141',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v3_lattices @ X0 )
      | ( X0
        = ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v3_lattices])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('145',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( l3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('146',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( ( k7_filter_1 @ X3 @ X2 )
        = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u2_lattices @ X3 ) @ ( u2_lattices @ X2 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u1_lattices @ X3 ) @ ( u1_lattices @ X2 ) ) ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_filter_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k7_filter_1 @ X0 @ X0 )
        = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u2_lattices @ X0 ) ) @ ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k7_filter_1 @ X0 @ X0 )
        = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u2_lattices @ X0 ) ) @ ( u1_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = X3 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g3_lattices @ ( u1_struct_0 @ X1 ) @ ( u2_lattices @ X1 ) @ ( u1_lattices @ X1 ) )
       != ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l2_lattices @ X1 )
      | ( ( u1_struct_0 @ X1 )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_filter_1 @ X1 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v3_lattices @ X0 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','162'])).

thf('164',plain,(
    ! [X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X1 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X1 ) )
      | ( ( u1_struct_0 @ ( k7_filter_1 @ X1 @ X1 ) )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ ( k7_filter_1 @ X1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ X1 @ X1 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X1 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) )
      | ( ( u1_struct_0 @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['139','168'])).

thf('170',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['134','173'])).

thf('175',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','178'])).

thf('180',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_A ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['130','185'])).

thf('187',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('194',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('195',plain,
    ( ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('197',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('199',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('200',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('201',plain,
    ( ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('203',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( v2_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','126','127','192','197','198','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v7_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','204'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('206',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v7_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('207',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v7_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v7_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('213',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','211','212'])).

thf('214',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','213'])).

thf('215',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','216'])).

thf('218',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('219',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('221',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(fc6_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A ) )
     => ( ( v1_funct_1 @ ( u1_lattices @ A ) )
        & ( v1_funct_2 @ ( u1_lattices @ A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) )
        & ( v1_binop_1 @ ( u1_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('222',plain,(
    ! [X17: $i] :
      ( ( v1_binop_1 @ ( u1_lattices @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_lattices @ X17 )
      | ~ ( v6_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_lattice2])).

thf('223',plain,
    ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('224',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('225',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(t23_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ B @ B ) @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                 => ( ( ( v1_binop_1 @ C @ A )
                      & ( v1_binop_1 @ D @ B ) )
                  <=> ( v1_binop_1 @ ( k6_filter_1 @ A @ B @ C @ D ) @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) )).

thf('226',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 ) ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X28 @ X26 @ X29 @ X27 ) @ ( k2_zfmisc_1 @ X28 @ X26 ) )
      | ( v1_binop_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_filter_1])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ ( u1_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_binop_1 @ ( u1_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['224','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ ( u1_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ~ ( v1_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['223','229'])).

thf('231',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('232',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('233',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('234',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('235',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('236',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('237',plain,
    ( ~ ( v1_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['230','231','232','233','234','235','236'])).

thf('238',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v6_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','237'])).

thf('239',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v6_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('240',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v6_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v6_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('246',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','244','245'])).

thf('247',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['221','246'])).

thf('248',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('249',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','249'])).

thf('251',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('252',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('254',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf(fc4_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_lattices @ A )
        & ( l2_lattices @ A ) )
     => ( ( v1_funct_1 @ ( u2_lattices @ A ) )
        & ( v1_funct_2 @ ( u2_lattices @ A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) )
        & ( v2_binop_1 @ ( u2_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('255',plain,(
    ! [X16: $i] :
      ( ( v2_binop_1 @ ( u2_lattices @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l2_lattices @ X16 )
      | ~ ( v5_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice2])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('257',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('258',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('259',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('261',plain,(
    ! [X0: $i] :
      ( ~ ( v3_lattices @ X0 )
      | ( X0
        = ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v3_lattices])).

thf('262',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('263',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('264',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('265',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('266',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) @ X20 ) ) )
      | ( X19 = X23 )
      | ( ( g3_lattices @ X20 @ X19 @ X21 )
       != ( g3_lattices @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[free_g3_lattices])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ X1 )
       != ( g3_lattices @ X4 @ X3 @ X2 ) )
      | ( ( u2_lattices @ X0 )
        = X3 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u2_lattices @ X0 )
        = X1 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X1 @ X2 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['264','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ( ( u2_lattices @ X0 )
        = X2 )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['263','268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u2_lattices @ X0 )
        = X2 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ( ( u2_lattices @ X0 )
        = X2 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['262','270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( ( u2_lattices @ X0 )
        = X2 )
      | ( ( g3_lattices @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X0 ) @ ( u1_lattices @ X0 ) )
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( u2_lattices @ X0 )
        = X2 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['261','272'])).

thf('274',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ ( u2_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) ) )
      | ( ( u2_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
        = X2 )
      | ~ ( l2_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l1_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( v3_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ ( g3_lattices @ X3 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['273'])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( v3_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ( ( u2_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
        = X1 )
      | ~ ( v1_funct_1 @ ( u1_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['260','274'])).

thf('276',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( u1_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) ) )
      | ( ( u2_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
        = X1 )
      | ~ ( l1_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( v3_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( g3_lattices @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,
    ( ~ ( v1_funct_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l2_lattices @ ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l3_lattices @ ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_lattices @ ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_lattices @ ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
    | ( ( u2_lattices @ ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['259','276'])).

thf('278',plain,(
    v1_funct_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','113','116'])).

thf('279',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('280',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('281',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('282',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('284',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('285',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('286',plain,
    ( ( k7_filter_1 @ sk_A @ sk_B )
    = ( g3_lattices @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('287',plain,
    ( ~ ( v3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['277','278','279','280','281','282','283','284','285','286'])).

thf('288',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['256','287'])).

thf('289',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('294',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('295',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 ) ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X32 @ X30 @ X33 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X30 ) )
      | ( v2_binop_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_filter_1])).

thf('296',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ ( u2_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['294','295'])).

thf('297',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_binop_1 @ ( u2_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['293','296'])).

thf('298',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ ( u2_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,
    ( ~ ( v2_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l2_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['292','298'])).

thf('300',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('301',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('303',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('305',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('306',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('307',plain,
    ( ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['305','306'])).

thf('308',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('310',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['307','310'])).

thf('312',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('313',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('314',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('315',plain,
    ( ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['313','314'])).

thf('316',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('317',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,
    ( ~ ( v2_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['299','300','303','304','311','312','317'])).

thf('319',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v5_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['255','318'])).

thf('320',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v5_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('321',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v5_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v5_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('327',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['319','325','326'])).

thf('328',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['254','327'])).

thf('329',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('330',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['253','330'])).

thf('332',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('333',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('335',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf(fc3_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A ) )
     => ( ( v1_funct_1 @ ( u2_lattices @ A ) )
        & ( v1_funct_2 @ ( u2_lattices @ A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) @ ( u1_struct_0 @ A ) )
        & ( v1_binop_1 @ ( u2_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('336',plain,(
    ! [X15: $i] :
      ( ( v1_binop_1 @ ( u2_lattices @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l2_lattices @ X15 )
      | ~ ( v4_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_lattice2])).

thf('337',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('338',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('339',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('340',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 ) ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X28 @ X26 @ X29 @ X27 ) @ ( k2_zfmisc_1 @ X28 @ X26 ) )
      | ( v1_binop_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_filter_1])).

thf('341',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ ( u2_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_binop_1 @ ( u2_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['338','341'])).

thf('343',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ ( u2_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l2_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['337','343'])).

thf('345',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('346',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('347',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('348',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['307','310'])).

thf('349',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('350',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('351',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['344','345','346','347','348','349','350'])).

thf('352',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v4_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['336','351'])).

thf('353',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v4_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('354',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v4_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('358',plain,(
    v4_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['355','356','357'])).

thf('359',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('360',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['352','358','359'])).

thf('361',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['335','360'])).

thf('362',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('363',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['361','362'])).

thf('364',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['334','363'])).

thf('365',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('366',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['364','365'])).

thf('367',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('368',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('369',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('370',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf(t41_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( r1_lattice2 @ ( u1_struct_0 @ A ) @ ( u1_lattices @ A ) @ ( u2_lattices @ A ) ) ) )).

thf('371',plain,(
    ! [X41: $i] :
      ( ( r1_lattice2 @ ( u1_struct_0 @ X41 ) @ ( u1_lattices @ X41 ) @ ( u2_lattices @ X41 ) )
      | ~ ( l3_lattices @ X41 )
      | ~ ( v10_lattices @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice2])).

thf('372',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('373',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('374',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('375',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( l3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('376',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('377',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('378',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['376','377'])).

thf('379',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['378'])).

thf('380',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['375','379'])).

thf('381',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['380'])).

thf('382',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['374','381'])).

thf('383',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['373','383'])).

thf('385',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('386',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf(t31_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ A @ A ) @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( k2_zfmisc_1 @ B @ B ) @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( k2_zfmisc_1 @ B @ B ) @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) @ B ) ) ) )
                         => ( ( ( r1_lattice2 @ A @ C @ D )
                              & ( r1_lattice2 @ B @ E @ F ) )
                          <=> ( r1_lattice2 @ ( k2_zfmisc_1 @ A @ B ) @ ( k6_filter_1 @ A @ B @ C @ E ) @ ( k6_filter_1 @ A @ B @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('387',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ X36 @ X34 ) @ ( k6_filter_1 @ X36 @ X34 @ X38 @ X39 ) @ ( k6_filter_1 @ X36 @ X34 @ X35 @ X37 ) )
      | ( r1_lattice2 @ X34 @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_filter_1])).

thf('388',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ( r1_lattice2 @ X3 @ X2 @ X4 )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ X3 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ X1 @ X2 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ ( u2_lattices @ X0 ) @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['386','387'])).

thf('389',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X1 ) @ X2 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X1 ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_lattice2 @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ ( u1_lattices @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_lattices @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['385','388'])).

thf('390',plain,
    ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['372','389'])).

thf('391',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('392',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('393',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('394',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('395',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('396',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('397',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l2_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('398',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( l1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('399',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( l3_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('400',plain,(
    ! [X0: $i] :
      ( ( v3_lattices @ ( k7_filter_1 @ X0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('401',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ ( k7_filter_1 @ X0 @ X0 ) )
        = ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l1_lattices @ ( k7_filter_1 @ X0 @ X0 ) )
      | ~ ( l2_lattices @ ( k7_filter_1 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('402',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['400','401'])).

thf('403',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['402','403','404'])).

thf('406',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['399','406'])).

thf('408',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('409',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['407','408','409'])).

thf('411',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['410'])).

thf('412',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['398','411'])).

thf('413',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('415',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['412','413','414'])).

thf('416',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['415'])).

thf('417',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,
    ( ~ ( l2_lattices @ ( k7_filter_1 @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['416','417'])).

thf('419',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['397','418'])).

thf('420',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['419','420','421'])).

thf('423',plain,
    ( ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['422'])).

thf('424',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('426',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('427',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('428',plain,
    ( ( v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_lattices @ sk_B ) ),
    inference('sup+',[status(thm)],['426','427'])).

thf('429',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('430',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['428','429'])).

thf('431',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('432',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('433',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('434',plain,
    ( ( m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_lattices @ sk_B ) ),
    inference('sup+',[status(thm)],['432','433'])).

thf('435',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('436',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['434','435'])).

thf('437',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('438',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('439',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('440',plain,
    ( ( m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l2_lattices @ sk_B ) ),
    inference('sup+',[status(thm)],['438','439'])).

thf('441',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('442',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['440','441'])).

thf('443',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('444',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('445',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('446',plain,
    ( ( v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l2_lattices @ sk_B ) ),
    inference('sup+',[status(thm)],['444','445'])).

thf('447',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('448',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['446','447'])).

thf('449',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('450',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('451',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('452',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,
    ( ~ ( r1_lattice2 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['390','391','392','393','394','395','396','425','430','431','436','437','442','443','448','449','450','451','452'])).

thf('454',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['371','453'])).

thf('455',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('456',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('457',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['454','455','456'])).

thf('458',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['370','457'])).

thf('459',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('460',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['458','459'])).

thf('461',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['369','460'])).

thf('462',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('463',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['461','462'])).

thf('464',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['368','463'])).

thf('465',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('466',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['464','465'])).

thf('467',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['367','466'])).

thf('468',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('469',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['467','468'])).

thf('470',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('471',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('472',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('473',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf(t40_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( r1_lattice2 @ ( u1_struct_0 @ A ) @ ( u2_lattices @ A ) @ ( u1_lattices @ A ) ) ) )).

thf('474',plain,(
    ! [X40: $i] :
      ( ( r1_lattice2 @ ( u1_struct_0 @ X40 ) @ ( u2_lattices @ X40 ) @ ( u1_lattices @ X40 ) )
      | ~ ( l3_lattices @ X40 )
      | ~ ( v10_lattices @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice2])).

thf('475',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('476',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('477',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('478',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ X36 @ X34 ) @ ( k6_filter_1 @ X36 @ X34 @ X38 @ X39 ) @ ( k6_filter_1 @ X36 @ X34 @ X35 @ X37 ) )
      | ( r1_lattice2 @ X34 @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_filter_1])).

thf('479',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ( r1_lattice2 @ X3 @ X2 @ X4 )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ X3 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ X1 @ X2 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_lattices @ X0 ) @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['477','478'])).

thf('480',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X2 ) @ ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_lattices @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_lattice2 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['476','479'])).

thf('481',plain,
    ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['475','480'])).

thf('482',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('483',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('484',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('485',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('486',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('487',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['307','310'])).

thf('488',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('489',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['446','447'])).

thf('490',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('491',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['440','441'])).

thf('492',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('493',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['434','435'])).

thf('494',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('495',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['428','429'])).

thf('496',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('497',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('498',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('499',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('500',plain,
    ( ~ ( r1_lattice2 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['481','482','483','484','485','486','487','488','489','490','491','492','493','494','495','496','497','498','499'])).

thf('501',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['474','500'])).

thf('502',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('503',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('504',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['501','502','503'])).

thf('505',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['473','504'])).

thf('506',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('507',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['505','506'])).

thf('508',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['472','507'])).

thf('509',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('510',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['508','509'])).

thf('511',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['471','510'])).

thf('512',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('513',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['511','512'])).

thf('514',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['470','513'])).

thf('515',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('516',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_B ) @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['514','515'])).

thf(t17_lattice2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( ( v1_binop_1 @ ( u2_lattices @ A ) @ ( u1_struct_0 @ A ) )
          & ( v2_binop_1 @ ( u2_lattices @ A ) @ ( u1_struct_0 @ A ) )
          & ( v1_binop_1 @ ( u1_lattices @ A ) @ ( u1_struct_0 @ A ) )
          & ( v2_binop_1 @ ( u1_lattices @ A ) @ ( u1_struct_0 @ A ) )
          & ( r1_lattice2 @ ( u1_struct_0 @ A ) @ ( u2_lattices @ A ) @ ( u1_lattices @ A ) )
          & ( r1_lattice2 @ ( u1_struct_0 @ A ) @ ( u1_lattices @ A ) @ ( u2_lattices @ A ) ) )
       => ( v10_lattices @ A ) ) ) )).

thf('517',plain,(
    ! [X25: $i] :
      ( ~ ( v1_binop_1 @ ( u2_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v2_binop_1 @ ( u2_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_binop_1 @ ( u1_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v2_binop_1 @ ( u1_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_lattice2 @ ( u1_struct_0 @ X25 ) @ ( u2_lattices @ X25 ) @ ( u1_lattices @ X25 ) )
      | ~ ( r1_lattice2 @ ( u1_struct_0 @ X25 ) @ ( u1_lattices @ X25 ) @ ( u2_lattices @ X25 ) )
      | ( v10_lattices @ X25 )
      | ~ ( l3_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t17_lattice2])).

thf('518',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v10_lattices @ sk_B )
    | ~ ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['516','517'])).

thf('519',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('520',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v10_lattices @ sk_B )
    | ~ ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['518','519'])).

thf('521',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r1_lattice2 @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_B ) @ ( u2_lattices @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['520'])).

thf('522',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['469','521'])).

thf('523',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['522'])).

thf('524',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['366','523'])).

thf('525',plain,
    ( ~ ( v2_binop_1 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['524'])).

thf('526',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_B )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['333','525'])).

thf('527',plain,
    ( ~ ( v1_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['526'])).

thf('528',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_B )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['252','527'])).

thf('529',plain,
    ( ~ ( v2_binop_1 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['528'])).

thf('530',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['219','529'])).

thf('531',plain,
    ( ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['530'])).

thf('532',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('533',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['531','532'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('534',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('535',plain,
    ( ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['533','534'])).

thf('536',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf(dt_l2_lattices,axiom,(
    ! [A: $i] :
      ( ( l2_lattices @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('537',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l2_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l2_lattices])).

thf('538',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['536','537'])).

thf('539',plain,
    ( ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['535','538'])).

thf('540',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_B ) ),
    inference(simplify,[status(thm)],['539'])).

thf('541',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('542',plain,
    ( ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['540','541'])).

thf('543',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('544',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l2_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l2_lattices])).

thf('545',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['543','544'])).

thf('546',plain,
    ( ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['542','545'])).

thf('547',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_B ) ),
    inference(simplify,[status(thm)],['546'])).

thf('548',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('549',plain,
    ( ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['547','548'])).

thf('550',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('551',plain,
    ( ~ ( v10_lattices @ sk_B )
   <= ~ ( v10_lattices @ sk_B ) ),
    inference(split,[status(esa)],['550'])).

thf('552',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['550'])).

thf('553',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('554',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['552','553'])).

thf('555',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( v2_struct_0 @ sk_B ) ),
    inference(split,[status(esa)],['550'])).

thf('556',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('557',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['555','556'])).

thf('558',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('559',plain,
    ( ~ ( l3_lattices @ sk_B )
   <= ~ ( l3_lattices @ sk_B ) ),
    inference(split,[status(esa)],['550'])).

thf('560',plain,(
    l3_lattices @ sk_B ),
    inference('sup-',[status(thm)],['558','559'])).

thf('561',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('562',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['550'])).

thf('563',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['561','562'])).

thf('564',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('565',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('566',plain,(
    ! [X18: $i] :
      ( ( v2_binop_1 @ ( u1_lattices @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_lattices @ X18 )
      | ~ ( v7_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_lattice2])).

thf('567',plain,
    ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('568',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('569',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('570',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 ) ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X32 @ X30 @ X33 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X30 ) )
      | ( v2_binop_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_filter_1])).

thf('571',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ X2 @ X1 )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['569','570'])).

thf('572',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_binop_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['568','571'])).

thf('573',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ X2 @ X1 )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['572'])).

thf('574',plain,
    ( ~ ( v2_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['567','573'])).

thf('575',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('576',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('577',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('578',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('579',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('580',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('581',plain,
    ( ~ ( v2_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['574','575','576','577','578','579','580'])).

thf('582',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v7_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['566','581'])).

thf('583',plain,(
    v7_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('584',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('585',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['582','583','584'])).

thf('586',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['565','585'])).

thf('587',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('588',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['586','587'])).

thf('589',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['564','588'])).

thf('590',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('591',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['589','590'])).

thf('592',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('593',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('594',plain,(
    ! [X17: $i] :
      ( ( v1_binop_1 @ ( u1_lattices @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_lattices @ X17 )
      | ~ ( v6_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_lattice2])).

thf('595',plain,
    ( ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_lattices @ sk_A ) @ ( u1_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('596',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ ( u1_lattices @ X12 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('597',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('598',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 ) ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X28 @ X26 @ X29 @ X27 ) @ ( k2_zfmisc_1 @ X28 @ X26 ) )
      | ( v1_binop_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_filter_1])).

thf('599',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ X2 @ X1 )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['597','598'])).

thf('600',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_binop_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['596','599'])).

thf('601',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ X2 @ X1 )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u1_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['600'])).

thf('602',plain,
    ( ~ ( v1_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['595','601'])).

thf('603',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('604',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('605',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('606',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('607',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('608',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('609',plain,
    ( ~ ( v1_binop_1 @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['602','603','604','605','606','607','608'])).

thf('610',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v6_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['594','609'])).

thf('611',plain,(
    v6_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('612',plain,(
    l1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('613',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['610','611','612'])).

thf('614',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['593','613'])).

thf('615',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('616',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['614','615'])).

thf('617',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['592','616'])).

thf('618',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('619',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['617','618'])).

thf('620',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('621',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('622',plain,(
    ! [X16: $i] :
      ( ( v2_binop_1 @ ( u2_lattices @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l2_lattices @ X16 )
      | ~ ( v5_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice2])).

thf('623',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('624',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('625',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('626',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) @ X30 ) ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X32 @ X30 @ X33 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X30 ) )
      | ( v2_binop_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( k2_zfmisc_1 @ X32 @ X32 ) @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_filter_1])).

thf('627',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ X2 @ X1 )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['625','626'])).

thf('628',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_binop_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['624','627'])).

thf('629',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v2_binop_1 @ X2 @ X1 )
      | ~ ( v2_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['628'])).

thf('630',plain,
    ( ~ ( v2_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l2_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['623','629'])).

thf('631',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('632',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('633',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('634',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['307','310'])).

thf('635',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('636',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('637',plain,
    ( ~ ( v2_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['630','631','632','633','634','635','636'])).

thf('638',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v5_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['622','637'])).

thf('639',plain,(
    v5_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('640',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('641',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['638','639','640'])).

thf('642',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['621','641'])).

thf('643',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('644',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['642','643'])).

thf('645',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['620','644'])).

thf('646',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('647',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['645','646'])).

thf('648',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('649',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('650',plain,(
    ! [X15: $i] :
      ( ( v1_binop_1 @ ( u2_lattices @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l2_lattices @ X15 )
      | ~ ( v4_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_lattice2])).

thf('651',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('652',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ ( u2_lattices @ X13 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('653',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('654',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) @ X26 ) ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X28 @ X26 @ X29 @ X27 ) @ ( k2_zfmisc_1 @ X28 @ X26 ) )
      | ( v1_binop_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( k2_zfmisc_1 @ X28 @ X28 ) @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_filter_1])).

thf('655',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ X2 @ X1 )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['653','654'])).

thf('656',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_binop_1 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['652','655'])).

thf('657',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) @ X1 ) ) )
      | ( v1_binop_1 @ X2 @ X1 )
      | ~ ( v1_binop_1 @ ( k6_filter_1 @ X1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( u2_lattices @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['656'])).

thf('658',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l2_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['651','657'])).

thf('659',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('660',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('661',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('662',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['307','310'])).

thf('663',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('664',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('665',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['658','659','660','661','662','663','664'])).

thf('666',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v4_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['650','665'])).

thf('667',plain,(
    v4_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['355','356','357'])).

thf('668',plain,(
    l2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('669',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['666','667','668'])).

thf('670',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['649','669'])).

thf('671',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('672',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['670','671'])).

thf('673',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['648','672'])).

thf('674',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('675',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['673','674'])).

thf('676',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('677',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('678',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('679',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('680',plain,(
    ! [X41: $i] :
      ( ( r1_lattice2 @ ( u1_struct_0 @ X41 ) @ ( u1_lattices @ X41 ) @ ( u2_lattices @ X41 ) )
      | ~ ( l3_lattices @ X41 )
      | ~ ( v10_lattices @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice2])).

thf('681',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('682',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('683',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u2_lattices @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('684',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ X36 @ X34 ) @ ( k6_filter_1 @ X36 @ X34 @ X38 @ X39 ) @ ( k6_filter_1 @ X36 @ X34 @ X35 @ X37 ) )
      | ( r1_lattice2 @ X36 @ X38 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_filter_1])).

thf('685',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ( r1_lattice2 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u2_lattices @ X0 ) )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ X3 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ X1 @ X2 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ ( u2_lattices @ X0 ) @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X0 ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['683','684'])).

thf('686',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u2_lattices @ X1 ) @ X2 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u2_lattices @ X1 ) )
      | ~ ( v1_funct_2 @ ( u2_lattices @ X1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_lattice2 @ ( u1_struct_0 @ X1 ) @ ( u1_lattices @ X1 ) @ ( u2_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( u1_lattices @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_lattices @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['682','685'])).

thf('687',plain,
    ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['681','686'])).

thf('688',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('689',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('690',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('691',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('692',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('693',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('694',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('695',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['428','429'])).

thf('696',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('697',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['434','435'])).

thf('698',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('699',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['440','441'])).

thf('700',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('701',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['446','447'])).

thf('702',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('703',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('704',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('705',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('706',plain,
    ( ~ ( r1_lattice2 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['687','688','689','690','691','692','693','694','695','696','697','698','699','700','701','702','703','704','705'])).

thf('707',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['680','706'])).

thf('708',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('709',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('710',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['707','708','709'])).

thf('711',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['679','710'])).

thf('712',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('713',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['711','712'])).

thf('714',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['678','713'])).

thf('715',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('716',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['714','715'])).

thf('717',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['677','716'])).

thf('718',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('719',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['717','718'])).

thf('720',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['676','719'])).

thf('721',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('722',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['720','721'])).

thf('723',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('724',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('725',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( u2_lattices @ X13 ) )
      | ~ ( l2_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u2_lattices])).

thf('726',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( u1_lattices @ X12 ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('727',plain,(
    ! [X40: $i] :
      ( ( r1_lattice2 @ ( u1_struct_0 @ X40 ) @ ( u2_lattices @ X40 ) @ ( u1_lattices @ X40 ) )
      | ~ ( l3_lattices @ X40 )
      | ~ ( v10_lattices @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice2])).

thf('728',plain,
    ( ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k6_filter_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u2_lattices @ sk_A ) @ ( u2_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('729',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
        = ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_lattices @ X1 ) @ ( u1_lattices @ X0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('730',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( u1_lattices @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_lattices])).

thf('731',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ X36 @ X34 ) @ ( k6_filter_1 @ X36 @ X34 @ X38 @ X39 ) @ ( k6_filter_1 @ X36 @ X34 @ X35 @ X37 ) )
      | ( r1_lattice2 @ X36 @ X38 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( k2_zfmisc_1 @ X34 @ X34 ) @ X34 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( k2_zfmisc_1 @ X36 @ X36 ) @ X36 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_filter_1])).

thf('732',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ( r1_lattice2 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_lattices @ X0 ) )
      | ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ X3 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ X1 @ X2 ) @ ( k6_filter_1 @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_lattices @ X0 ) @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( k2_zfmisc_1 @ X3 @ X3 ) @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['730','731'])).

thf('733',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) @ ( k6_filter_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X2 ) @ ( u1_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X1 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( u1_lattices @ X0 ) )
      | ~ ( v1_funct_2 @ ( u1_lattices @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_lattices @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_lattice2 @ ( u1_struct_0 @ X1 ) @ X3 @ ( u1_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['729','732'])).

thf('734',plain,
    ( ~ ( r1_lattice2 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['728','733'])).

thf('735',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('736',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('737',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('738',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('739',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('740',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['307','310'])).

thf('741',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('742',plain,(
    v1_funct_2 @ ( u2_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['446','447'])).

thf('743',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('744',plain,(
    m1_subset_1 @ ( u2_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['440','441'])).

thf('745',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('746',plain,(
    m1_subset_1 @ ( u1_lattices @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['434','435'])).

thf('747',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('748',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_B ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_B @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['428','429'])).

thf('749',plain,
    ( ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) )
    = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('750',plain,(
    v1_funct_2 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('751',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('752',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('753',plain,
    ( ~ ( r1_lattice2 @ ( u1_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u2_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) @ ( u1_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['734','735','736','737','738','739','740','741','742','743','744','745','746','747','748','749','750','751','752'])).

thf('754',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['727','753'])).

thf('755',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('756',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('757',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['754','755','756'])).

thf('758',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['726','757'])).

thf('759',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('760',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['758','759'])).

thf('761',plain,
    ( ~ ( l2_lattices @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['725','760'])).

thf('762',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['308','309'])).

thf('763',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['761','762'])).

thf('764',plain,
    ( ~ ( l1_lattices @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['724','763'])).

thf('765',plain,(
    l1_lattices @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('766',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( u2_lattices @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['764','765'])).

thf('767',plain,
    ( ~ ( l2_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['723','766'])).

thf('768',plain,(
    l2_lattices @ sk_B ),
    inference('sup-',[status(thm)],['301','302'])).

thf('769',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u2_lattices @ sk_A ) @ ( u1_lattices @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['767','768'])).

thf('770',plain,(
    ! [X25: $i] :
      ( ~ ( v1_binop_1 @ ( u2_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v2_binop_1 @ ( u2_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_binop_1 @ ( u1_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v2_binop_1 @ ( u1_lattices @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_lattice2 @ ( u1_struct_0 @ X25 ) @ ( u2_lattices @ X25 ) @ ( u1_lattices @ X25 ) )
      | ~ ( r1_lattice2 @ ( u1_struct_0 @ X25 ) @ ( u1_lattices @ X25 ) @ ( u2_lattices @ X25 ) )
      | ( v10_lattices @ X25 )
      | ~ ( l3_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t17_lattice2])).

thf('771',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v10_lattices @ sk_A )
    | ~ ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['769','770'])).

thf('772',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('773',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A )
    | ~ ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['771','772'])).

thf('774',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice2 @ ( u1_struct_0 @ sk_A ) @ ( u1_lattices @ sk_A ) @ ( u2_lattices @ sk_A ) )
    | ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['773'])).

thf('775',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v10_lattices @ sk_A )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['722','774'])).

thf('776',plain,
    ( ~ ( v1_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['775'])).

thf('777',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v10_lattices @ sk_A )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['675','776'])).

thf('778',plain,
    ( ~ ( v2_binop_1 @ ( u2_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['777'])).

thf('779',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['647','778'])).

thf('780',plain,
    ( ~ ( v1_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['779'])).

thf('781',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A )
    | ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['619','780'])).

thf('782',plain,
    ( ~ ( v2_binop_1 @ ( u1_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['781'])).

thf('783',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['591','782'])).

thf('784',plain,
    ( ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['783'])).

thf('785',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('786',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['784','785'])).

thf('787',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('788',plain,
    ( ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['786','787'])).

thf('789',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['536','537'])).

thf('790',plain,
    ( ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['788','789'])).

thf('791',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A ) ),
    inference(simplify,[status(thm)],['790'])).

thf('792',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('793',plain,
    ( ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['791','792'])).

thf('794',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['543','544'])).

thf('795',plain,
    ( ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['793','794'])).

thf('796',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v10_lattices @ sk_A ) ),
    inference(simplify,[status(thm)],['795'])).

thf('797',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('798',plain,
    ( ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['796','797'])).

thf('799',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('800',plain,(
    v10_lattices @ sk_A ),
    inference(clc,[status(thm)],['798','799'])).

thf('801',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['550'])).

thf('802',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['800','801'])).

thf('803',plain,
    ( ~ ( v10_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['550'])).

thf('804',plain,(
    ~ ( v10_lattices @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['554','557','560','563','802','803'])).

thf('805',plain,(
    ~ ( v10_lattices @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['551','804'])).

thf('806',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['549','805'])).

thf('807',plain,(
    $false ),
    inference(demod,[status(thm)],['0','806'])).


%------------------------------------------------------------------------------
