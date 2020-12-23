%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ne8eFWGF47

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:34 EST 2020

% Result     : Theorem 8.21s
% Output     : Refutation 8.21s
% Verified   : 
% Statistics : Number of formulae       :  280 (2968 expanded)
%              Number of leaves         :   35 ( 816 expanded)
%              Depth                    :   53
%              Number of atoms          : 4125 (68931 expanded)
%              Number of equality atoms :   57 ( 140 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(a_2_5_lattice3_type,type,(
    a_2_5_lattice3: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(a_2_6_lattice3_type,type,(
    a_2_6_lattice3: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(t48_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i,C: $i] :
          ( ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_hidden @ D @ B )
                  & ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r3_lattices @ A @ D @ E )
                          & ( r2_hidden @ E @ C ) ) ) ) )
         => ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ D @ B )
                    & ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r3_lattices @ A @ D @ E )
                            & ( r2_hidden @ E @ C ) ) ) ) )
           => ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ( k16_lattice3 @ A @ B )
            = ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) )
          & ( ( k15_lattice3 @ A @ B )
            = ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X35: $i] :
      ( ( ( k15_lattice3 @ X33 @ X35 )
        = ( k15_lattice3 @ X33 @ ( a_2_5_lattice3 @ X33 @ X35 ) ) )
      | ~ ( l3_lattices @ X33 )
      | ~ ( v4_lattice3 @ X33 )
      | ~ ( v10_lattices @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf(t37_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k15_lattice3 @ X26 @ X27 )
        = ( k16_lattice3 @ X26 @ ( a_2_2_lattice3 @ X26 @ X27 ) ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf(d18_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v4_lattice3 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r4_lattice3 @ A @ D @ B )
                 => ( r1_lattices @ A @ C @ D ) ) )
            & ( r4_lattice3 @ A @ C @ B )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf(d17_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r4_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r4_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r4_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X36: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ X36 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X36 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ sk_C_1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ sk_C_1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ sk_C_1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('26',plain,(
    ! [X36: $i] :
      ( ( r3_lattices @ sk_A @ X36 @ ( sk_E_1 @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('40',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ X36 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X36 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ X1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf(fraenkel_a_2_5_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ? [E: $i] :
                ( ( r2_hidden @ E @ C )
                & ( r3_lattices @ B @ D @ E )
                & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( r2_hidden @ X23 @ ( a_2_5_lattice3 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ( X23 != X24 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( r3_lattices @ X21 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_lattices @ X21 @ X24 @ X25 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X24 @ ( a_2_5_lattice3 @ X21 @ X22 ) )
      | ( v2_struct_0 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( l3_lattices @ X21 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X2 @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ X2 @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X2 @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ X2 @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ X1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( X23
        = ( sk_D_4 @ X22 @ X21 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ ( a_2_5_lattice3 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
        = ( sk_D_4 @ sk_C_1 @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
        = ( sk_D_4 @ sk_C_1 @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
        = ( sk_D_4 @ sk_C_1 @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( sk_D_4 @ X22 @ X21 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X23 @ ( a_2_5_lattice3 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D_4 @ sk_C_1 @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D_4 @ sk_C_1 @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ sk_C_1 @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('91',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('92',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('106',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ ( sk_D @ X8 @ X4 @ X5 ) @ X4 )
      | ( r4_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( sk_C @ X1 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','108'])).

thf('110',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf(fraenkel_a_2_2_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r4_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('117',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( X19 != X20 )
      | ~ ( r4_lattice3 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('118',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r4_lattice3 @ X17 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X20 @ ( a_2_2_lattice3 @ X17 @ X18 ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( l3_lattices @ X17 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['116','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r2_hidden @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf(t38_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ B @ C )
             => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) )).

thf('129',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r3_lattices @ X29 @ ( k16_lattice3 @ X29 @ X30 ) @ X28 )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v4_lattice3 @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X2 ) @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X2 ) @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['2','138'])).

thf('140',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    r2_hidden @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('147',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( m1_subset_1 @ ( sk_D_3 @ X18 @ X17 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('148',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    r2_hidden @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('156',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( X19
        = ( sk_D_3 @ X18 @ X17 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('157',plain,
    ( ( ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A )
      = ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A )
      = ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A )
    = ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    m1_subset_1 @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','163'])).

thf('165',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('166',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf(d21_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ( ( C
                = ( k15_lattice3 @ A @ B ) )
            <=> ( ( r4_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r4_lattice3 @ A @ D @ B )
                     => ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('167',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ( r4_lattice3 @ X13 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ X15 )
      | ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('168',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ( r4_lattice3 @ X13 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ X15 )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['166','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('174',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('175',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('176',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['174','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ~ ( r4_lattice3 @ X10 @ X12 @ X11 )
      | ( r1_lattices @ X10 @ ( sk_C @ X11 @ X10 ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['172','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( r1_lattices @ X13 @ X14 @ ( sk_D_2 @ X14 @ X15 @ X13 ) )
      | ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('187',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( r1_lattices @ X13 @ X14 @ ( sk_D_2 @ X14 @ X15 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['185','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A )
      = ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) )
    | ~ ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['164','189'])).

thf('191',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','163'])).

thf(t43_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B )
            & ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B ) ) ) ) )).

thf('195',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k16_lattice3 @ X32 @ ( k6_domain_1 @ ( u1_struct_0 @ X32 ) @ X31 ) )
        = X31 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) )
      = ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) )
      = ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) )
    = ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( X19
        = ( sk_D_3 @ X18 @ X17 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('211',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( m1_subset_1 @ ( sk_D_3 @ X18 @ X17 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k16_lattice3 @ X32 @ ( k6_domain_1 @ ( u1_struct_0 @ X32 ) @ X31 ) )
        = X31 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k16_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) )
        = ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k16_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) )
        = ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k16_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) )
        = ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['209','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k16_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) )
        = ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('220',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( r4_lattice3 @ X17 @ ( sk_D_3 @ X18 @ X17 @ X19 ) @ X18 )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['218','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r4_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['202','224'])).

thf('226',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    r4_lattice3 @ sk_A @ ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A )
      = ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( sk_C @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) @ sk_A )
    = ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['145','234'])).

thf('236',plain,
    ( ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','235'])).

thf('237',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,(
    ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['0','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ne8eFWGF47
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:37:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 8.21/8.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.21/8.44  % Solved by: fo/fo7.sh
% 8.21/8.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.21/8.44  % done 7754 iterations in 7.965s
% 8.21/8.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.21/8.44  % SZS output start Refutation
% 8.21/8.44  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 8.21/8.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 8.21/8.44  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 8.21/8.44  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 8.21/8.44  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 8.21/8.44  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 8.21/8.44  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 8.21/8.44  thf(a_2_5_lattice3_type, type, a_2_5_lattice3: $i > $i > $i).
% 8.21/8.44  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 8.21/8.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.21/8.44  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 8.21/8.44  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 8.21/8.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.21/8.44  thf(a_2_6_lattice3_type, type, a_2_6_lattice3: $i > $i > $i).
% 8.21/8.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.21/8.44  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 8.21/8.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.21/8.44  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.21/8.44  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 8.21/8.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.21/8.44  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 8.21/8.44  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 8.21/8.44  thf(sk_A_type, type, sk_A: $i).
% 8.21/8.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.21/8.44  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 8.21/8.44  thf(t48_lattice3, conjecture,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ![B:$i,C:$i]:
% 8.21/8.44         ( ( ![D:$i]:
% 8.21/8.44             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44               ( ~( ( r2_hidden @ D @ B ) & 
% 8.21/8.44                    ( ![E:$i]:
% 8.21/8.44                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 8.21/8.44                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 8.21/8.44           ( r3_lattices @
% 8.21/8.44             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 8.21/8.44  thf(zf_stmt_0, negated_conjecture,
% 8.21/8.44    (~( ![A:$i]:
% 8.21/8.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44          ( ![B:$i,C:$i]:
% 8.21/8.44            ( ( ![D:$i]:
% 8.21/8.44                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44                  ( ~( ( r2_hidden @ D @ B ) & 
% 8.21/8.44                       ( ![E:$i]:
% 8.21/8.44                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44                           ( ~( ( r3_lattices @ A @ D @ E ) & 
% 8.21/8.44                                ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 8.21/8.44              ( r3_lattices @
% 8.21/8.44                A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ) )),
% 8.21/8.44    inference('cnf.neg', [status(esa)], [t48_lattice3])).
% 8.21/8.44  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf(t47_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ![B:$i]:
% 8.21/8.44         ( ( ( k16_lattice3 @ A @ B ) =
% 8.21/8.44             ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) ) & 
% 8.21/8.44           ( ( k15_lattice3 @ A @ B ) =
% 8.21/8.44             ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) ))).
% 8.21/8.44  thf('1', plain,
% 8.21/8.44      (![X33 : $i, X35 : $i]:
% 8.21/8.44         (((k15_lattice3 @ X33 @ X35)
% 8.21/8.44            = (k15_lattice3 @ X33 @ (a_2_5_lattice3 @ X33 @ X35)))
% 8.21/8.44          | ~ (l3_lattices @ X33)
% 8.21/8.44          | ~ (v4_lattice3 @ X33)
% 8.21/8.44          | ~ (v10_lattices @ X33)
% 8.21/8.44          | (v2_struct_0 @ X33))),
% 8.21/8.44      inference('cnf', [status(esa)], [t47_lattice3])).
% 8.21/8.44  thf(t37_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ![B:$i]:
% 8.21/8.44         ( ( k15_lattice3 @ A @ B ) =
% 8.21/8.44           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 8.21/8.44  thf('2', plain,
% 8.21/8.44      (![X26 : $i, X27 : $i]:
% 8.21/8.44         (((k15_lattice3 @ X26 @ X27)
% 8.21/8.44            = (k16_lattice3 @ X26 @ (a_2_2_lattice3 @ X26 @ X27)))
% 8.21/8.44          | ~ (l3_lattices @ X26)
% 8.21/8.44          | ~ (v4_lattice3 @ X26)
% 8.21/8.44          | ~ (v10_lattices @ X26)
% 8.21/8.44          | (v2_struct_0 @ X26))),
% 8.21/8.44      inference('cnf', [status(esa)], [t37_lattice3])).
% 8.21/8.44  thf(d18_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ( v4_lattice3 @ A ) <=>
% 8.21/8.44         ( ![B:$i]:
% 8.21/8.44           ( ?[C:$i]:
% 8.21/8.44             ( ( ![D:$i]:
% 8.21/8.44                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44                   ( ( r4_lattice3 @ A @ D @ B ) => ( r1_lattices @ A @ C @ D ) ) ) ) & 
% 8.21/8.44               ( r4_lattice3 @ A @ C @ B ) & 
% 8.21/8.44               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 8.21/8.44  thf('3', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf(d17_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ![B:$i]:
% 8.21/8.44         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44           ( ![C:$i]:
% 8.21/8.44             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 8.21/8.44               ( ![D:$i]:
% 8.21/8.44                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 8.21/8.44  thf('4', plain,
% 8.21/8.44      (![X4 : $i, X5 : $i, X8 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 8.21/8.44          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 8.21/8.44          | (r4_lattice3 @ X5 @ X4 @ X8)
% 8.21/8.44          | ~ (l3_lattices @ X5)
% 8.21/8.44          | (v2_struct_0 @ X5))),
% 8.21/8.44      inference('cnf', [status(esa)], [d17_lattice3])).
% 8.21/8.44  thf('5', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2))),
% 8.21/8.44      inference('sup-', [status(thm)], ['3', '4'])).
% 8.21/8.44  thf('6', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['5'])).
% 8.21/8.44  thf('7', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('8', plain,
% 8.21/8.44      (![X4 : $i, X5 : $i, X8 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 8.21/8.44          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 8.21/8.44          | (r4_lattice3 @ X5 @ X4 @ X8)
% 8.21/8.44          | ~ (l3_lattices @ X5)
% 8.21/8.44          | (v2_struct_0 @ X5))),
% 8.21/8.44      inference('cnf', [status(esa)], [d17_lattice3])).
% 8.21/8.44  thf('9', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44             (u1_struct_0 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['7', '8'])).
% 8.21/8.44  thf('10', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44           (u1_struct_0 @ X0))
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.21/8.44  thf('11', plain,
% 8.21/8.44      (![X36 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_E_1 @ X36) @ sk_C_1)
% 8.21/8.44          | ~ (r2_hidden @ X36 @ sk_B_1)
% 8.21/8.44          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('12', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ X1)
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ (sk_E_1 @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             sk_C_1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['10', '11'])).
% 8.21/8.44  thf('13', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('14', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('15', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ X1)
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ (sk_E_1 @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             sk_C_1))),
% 8.21/8.44      inference('demod', [status(thm)], ['12', '13', '14'])).
% 8.21/8.44  thf('16', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ sk_C_1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['6', '15'])).
% 8.21/8.44  thf('17', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('18', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('19', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ sk_C_1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['16', '17', '18'])).
% 8.21/8.44  thf('20', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r2_hidden @ 
% 8.21/8.44           (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ sk_C_1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('simplify', [status(thm)], ['19'])).
% 8.21/8.44  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('22', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ sk_C_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['20', '21'])).
% 8.21/8.44  thf('23', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44           (u1_struct_0 @ X0))
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.21/8.44  thf('24', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['5'])).
% 8.21/8.44  thf('25', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44           (u1_struct_0 @ X0))
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.21/8.44  thf('26', plain,
% 8.21/8.44      (![X36 : $i]:
% 8.21/8.44         ((r3_lattices @ sk_A @ X36 @ (sk_E_1 @ X36))
% 8.21/8.44          | ~ (r2_hidden @ X36 @ sk_B_1)
% 8.21/8.44          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('27', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ X1)
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r3_lattices @ sk_A @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['25', '26'])).
% 8.21/8.44  thf('28', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('29', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('30', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ X1)
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r3_lattices @ sk_A @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A))))),
% 8.21/8.44      inference('demod', [status(thm)], ['27', '28', '29'])).
% 8.21/8.44  thf('31', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r3_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['24', '30'])).
% 8.21/8.44  thf('32', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('33', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('34', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r3_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['31', '32', '33'])).
% 8.21/8.44  thf('35', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r3_lattices @ sk_A @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44           (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('simplify', [status(thm)], ['34'])).
% 8.21/8.44  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('37', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r3_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A))))),
% 8.21/8.44      inference('clc', [status(thm)], ['35', '36'])).
% 8.21/8.44  thf('38', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['5'])).
% 8.21/8.44  thf('39', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44           (u1_struct_0 @ X0))
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['9'])).
% 8.21/8.44  thf('40', plain,
% 8.21/8.44      (![X36 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_E_1 @ X36) @ (u1_struct_0 @ sk_A))
% 8.21/8.44          | ~ (r2_hidden @ X36 @ sk_B_1)
% 8.21/8.44          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('41', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ X1)
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['39', '40'])).
% 8.21/8.44  thf('42', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('43', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('44', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ X1)
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ X1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('demod', [status(thm)], ['41', '42', '43'])).
% 8.21/8.44  thf('45', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['38', '44'])).
% 8.21/8.44  thf('46', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('47', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('48', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['45', '46', '47'])).
% 8.21/8.44  thf('49', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((m1_subset_1 @ 
% 8.21/8.44           (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44           (u1_struct_0 @ sk_A))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('simplify', [status(thm)], ['48'])).
% 8.21/8.44  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('51', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('clc', [status(thm)], ['49', '50'])).
% 8.21/8.44  thf(fraenkel_a_2_5_lattice3, axiom,
% 8.21/8.44    (![A:$i,B:$i,C:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 8.21/8.44         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 8.21/8.44       ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) ) <=>
% 8.21/8.44         ( ?[D:$i]:
% 8.21/8.44           ( ( ?[E:$i]:
% 8.21/8.44               ( ( r2_hidden @ E @ C ) & ( r3_lattices @ B @ D @ E ) & 
% 8.21/8.44                 ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.21/8.44             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 8.21/8.44  thf('52', plain,
% 8.21/8.44      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X21)
% 8.21/8.44          | ~ (v4_lattice3 @ X21)
% 8.21/8.44          | ~ (v10_lattices @ X21)
% 8.21/8.44          | (v2_struct_0 @ X21)
% 8.21/8.44          | (r2_hidden @ X23 @ (a_2_5_lattice3 @ X21 @ X22))
% 8.21/8.44          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 8.21/8.44          | ((X23) != (X24))
% 8.21/8.44          | ~ (r2_hidden @ X25 @ X22)
% 8.21/8.44          | ~ (r3_lattices @ X21 @ X24 @ X25)
% 8.21/8.44          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 8.21/8.44  thf('53', plain,
% 8.21/8.44      (![X21 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21))
% 8.21/8.44          | ~ (r3_lattices @ X21 @ X24 @ X25)
% 8.21/8.44          | ~ (r2_hidden @ X25 @ X22)
% 8.21/8.44          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 8.21/8.44          | (r2_hidden @ X24 @ (a_2_5_lattice3 @ X21 @ X22))
% 8.21/8.44          | (v2_struct_0 @ X21)
% 8.21/8.44          | ~ (v10_lattices @ X21)
% 8.21/8.44          | ~ (v4_lattice3 @ X21)
% 8.21/8.44          | ~ (l3_lattices @ X21))),
% 8.21/8.44      inference('simplify', [status(thm)], ['52'])).
% 8.21/8.44  thf('54', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | ~ (v10_lattices @ sk_A)
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r2_hidden @ X2 @ (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | ~ (r3_lattices @ sk_A @ X2 @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['51', '53'])).
% 8.21/8.44  thf('55', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('56', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('57', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('58', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r2_hidden @ X2 @ (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | ~ (r3_lattices @ sk_A @ X2 @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A))))),
% 8.21/8.44      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 8.21/8.44  thf('59', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | ~ (m1_subset_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44               (u1_struct_0 @ sk_A))
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['37', '58'])).
% 8.21/8.44  thf('60', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | ~ (m1_subset_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44               (u1_struct_0 @ sk_A))
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['59'])).
% 8.21/8.44  thf('61', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['23', '60'])).
% 8.21/8.44  thf('62', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('63', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('64', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['61', '62', '63'])).
% 8.21/8.44  thf('65', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44           (a_2_5_lattice3 @ sk_A @ X1))
% 8.21/8.44          | ~ (r2_hidden @ 
% 8.21/8.44               (sk_E_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ X1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('simplify', [status(thm)], ['64'])).
% 8.21/8.44  thf('66', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['22', '65'])).
% 8.21/8.44  thf('67', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44           (a_2_5_lattice3 @ sk_A @ sk_C_1))
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['66'])).
% 8.21/8.44  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('69', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('clc', [status(thm)], ['67', '68'])).
% 8.21/8.44  thf('70', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('clc', [status(thm)], ['67', '68'])).
% 8.21/8.44  thf('71', plain,
% 8.21/8.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X21)
% 8.21/8.44          | ~ (v4_lattice3 @ X21)
% 8.21/8.44          | ~ (v10_lattices @ X21)
% 8.21/8.44          | (v2_struct_0 @ X21)
% 8.21/8.44          | ((X23) = (sk_D_4 @ X22 @ X21 @ X23))
% 8.21/8.44          | ~ (r2_hidden @ X23 @ (a_2_5_lattice3 @ X21 @ X22)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 8.21/8.44  thf('72', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | ((sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 8.21/8.44              = (sk_D_4 @ sk_C_1 @ sk_A @ 
% 8.21/8.44                 (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)))
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (v10_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['70', '71'])).
% 8.21/8.44  thf('73', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('74', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('75', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('76', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | ((sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 8.21/8.44              = (sk_D_4 @ sk_C_1 @ sk_A @ 
% 8.21/8.44                 (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)))
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 8.21/8.44  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('78', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         (((sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 8.21/8.44            = (sk_D_4 @ sk_C_1 @ sk_A @ 
% 8.21/8.44               (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['76', '77'])).
% 8.21/8.44  thf('79', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('clc', [status(thm)], ['67', '68'])).
% 8.21/8.44  thf('80', plain,
% 8.21/8.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X21)
% 8.21/8.44          | ~ (v4_lattice3 @ X21)
% 8.21/8.44          | ~ (v10_lattices @ X21)
% 8.21/8.44          | (v2_struct_0 @ X21)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_4 @ X22 @ X21 @ X23) @ (u1_struct_0 @ X21))
% 8.21/8.44          | ~ (r2_hidden @ X23 @ (a_2_5_lattice3 @ X21 @ X22)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 8.21/8.44  thf('81', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_D_4 @ sk_C_1 @ sk_A @ 
% 8.21/8.44              (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A))
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (v10_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['79', '80'])).
% 8.21/8.44  thf('82', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('83', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('84', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('85', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ 
% 8.21/8.44             (sk_D_4 @ sk_C_1 @ sk_A @ 
% 8.21/8.44              (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A))
% 8.21/8.44          | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 8.21/8.44  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('87', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((m1_subset_1 @ 
% 8.21/8.44           (sk_D_4 @ sk_C_1 @ sk_A @ 
% 8.21/8.44            (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A)) @ 
% 8.21/8.44           (u1_struct_0 @ sk_A))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['85', '86'])).
% 8.21/8.44  thf('88', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44           (u1_struct_0 @ sk_A))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('sup+', [status(thm)], ['78', '87'])).
% 8.21/8.44  thf('89', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (m1_subset_1 @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (u1_struct_0 @ sk_A)))),
% 8.21/8.44      inference('simplify', [status(thm)], ['88'])).
% 8.21/8.44  thf('90', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('91', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('92', plain,
% 8.21/8.44      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 8.21/8.44          | ~ (r4_lattice3 @ X5 @ X4 @ X6)
% 8.21/8.44          | ~ (r2_hidden @ X7 @ X6)
% 8.21/8.44          | (r1_lattices @ X5 @ X7 @ X4)
% 8.21/8.44          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 8.21/8.44          | ~ (l3_lattices @ X5)
% 8.21/8.44          | (v2_struct_0 @ X5))),
% 8.21/8.44      inference('cnf', [status(esa)], [d17_lattice3])).
% 8.21/8.44  thf('93', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 8.21/8.44          | (r1_lattices @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 8.21/8.44          | ~ (r2_hidden @ X2 @ X3)
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X3))),
% 8.21/8.44      inference('sup-', [status(thm)], ['91', '92'])).
% 8.21/8.44  thf('94', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.21/8.44         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X3)
% 8.21/8.44          | ~ (r2_hidden @ X2 @ X3)
% 8.21/8.44          | (r1_lattices @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 8.21/8.44          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['93'])).
% 8.21/8.44  thf('95', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 8.21/8.44          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 8.21/8.44          | ~ (r2_hidden @ X2 @ X0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['90', '94'])).
% 8.21/8.44  thf('96', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (~ (r2_hidden @ X2 @ X0)
% 8.21/8.44          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 8.21/8.44          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['95'])).
% 8.21/8.44  thf('97', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | ~ (l3_lattices @ sk_A)
% 8.21/8.44          | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44          | (r1_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ (sk_C @ X1 @ sk_A))
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ X1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['89', '96'])).
% 8.21/8.44  thf('98', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('99', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('100', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r1_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ (sk_C @ X1 @ sk_A))
% 8.21/8.44          | ~ (r2_hidden @ (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ X1))),
% 8.21/8.44      inference('demod', [status(thm)], ['97', '98', '99'])).
% 8.21/8.44  thf('101', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r1_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))
% 8.21/8.44          | (v2_struct_0 @ sk_A)
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['69', '100'])).
% 8.21/8.44  thf('102', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((v2_struct_0 @ sk_A)
% 8.21/8.44          | (r1_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))
% 8.21/8.44          | (r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['101'])).
% 8.21/8.44  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('104', plain,
% 8.21/8.44      (![X0 : $i]:
% 8.21/8.44         ((r4_lattice3 @ sk_A @ (sk_C @ X0 @ sk_A) @ sk_B_1)
% 8.21/8.44          | (r1_lattices @ sk_A @ 
% 8.21/8.44             (sk_D @ sk_B_1 @ (sk_C @ X0 @ sk_A) @ sk_A) @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 8.21/8.44      inference('clc', [status(thm)], ['102', '103'])).
% 8.21/8.44  thf('105', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('106', plain,
% 8.21/8.44      (![X4 : $i, X5 : $i, X8 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 8.21/8.44          | ~ (r1_lattices @ X5 @ (sk_D @ X8 @ X4 @ X5) @ X4)
% 8.21/8.44          | (r4_lattice3 @ X5 @ X4 @ X8)
% 8.21/8.44          | ~ (l3_lattices @ X5)
% 8.21/8.44          | (v2_struct_0 @ X5))),
% 8.21/8.44      inference('cnf', [status(esa)], [d17_lattice3])).
% 8.21/8.44  thf('107', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (r1_lattices @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44               (sk_C @ X1 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['105', '106'])).
% 8.21/8.44  thf('108', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (~ (r1_lattices @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 8.21/8.44             (sk_C @ X1 @ X0))
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['107'])).
% 8.21/8.44  thf('109', plain,
% 8.21/8.44      (((r4_lattice3 @ sk_A @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ sk_B_1)
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | (r4_lattice3 @ sk_A @ 
% 8.21/8.44           (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['104', '108'])).
% 8.21/8.44  thf('110', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('111', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('112', plain,
% 8.21/8.44      (((r4_lattice3 @ sk_A @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ sk_B_1)
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | (r4_lattice3 @ sk_A @ 
% 8.21/8.44           (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('demod', [status(thm)], ['109', '110', '111'])).
% 8.21/8.44  thf('113', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | (r4_lattice3 @ sk_A @ 
% 8.21/8.44           (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ sk_B_1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['112'])).
% 8.21/8.44  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('115', plain,
% 8.21/8.44      ((r4_lattice3 @ sk_A @ 
% 8.21/8.44        (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ sk_B_1)),
% 8.21/8.44      inference('clc', [status(thm)], ['113', '114'])).
% 8.21/8.44  thf('116', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf(fraenkel_a_2_2_lattice3, axiom,
% 8.21/8.44    (![A:$i,B:$i,C:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 8.21/8.44         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 8.21/8.44       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 8.21/8.44         ( ?[D:$i]:
% 8.21/8.44           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 8.21/8.44             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 8.21/8.44  thf('117', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18))
% 8.21/8.44          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 8.21/8.44          | ((X19) != (X20))
% 8.21/8.44          | ~ (r4_lattice3 @ X17 @ X20 @ X18))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 8.21/8.44  thf('118', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X20 : $i]:
% 8.21/8.44         (~ (r4_lattice3 @ X17 @ X20 @ X18)
% 8.21/8.44          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 8.21/8.44          | (r2_hidden @ X20 @ (a_2_2_lattice3 @ X17 @ X18))
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (l3_lattices @ X17))),
% 8.21/8.44      inference('simplify', [status(thm)], ['117'])).
% 8.21/8.44  thf('119', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X2))
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2))),
% 8.21/8.44      inference('sup-', [status(thm)], ['116', '118'])).
% 8.21/8.44  thf('120', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X2))
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['119'])).
% 8.21/8.44  thf('121', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | (r2_hidden @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['115', '120'])).
% 8.21/8.44  thf('122', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('123', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('124', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('125', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | (r2_hidden @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 8.21/8.44      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 8.21/8.44  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('127', plain,
% 8.21/8.44      ((r2_hidden @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['125', '126'])).
% 8.21/8.44  thf('128', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf(t38_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ![B:$i]:
% 8.21/8.44         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44           ( ![C:$i]:
% 8.21/8.44             ( ( r2_hidden @ B @ C ) =>
% 8.21/8.44               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 8.21/8.44                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 8.21/8.44  thf('129', plain,
% 8.21/8.44      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 8.21/8.44          | (r3_lattices @ X29 @ (k16_lattice3 @ X29 @ X30) @ X28)
% 8.21/8.44          | ~ (r2_hidden @ X28 @ X30)
% 8.21/8.44          | ~ (l3_lattices @ X29)
% 8.21/8.44          | ~ (v4_lattice3 @ X29)
% 8.21/8.44          | ~ (v10_lattices @ X29)
% 8.21/8.44          | (v2_struct_0 @ X29))),
% 8.21/8.44      inference('cnf', [status(esa)], [t38_lattice3])).
% 8.21/8.44  thf('130', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X2) @ (sk_C @ X1 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['128', '129'])).
% 8.21/8.44  thf('131', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X2) @ (sk_C @ X1 @ X0))
% 8.21/8.44          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['130'])).
% 8.21/8.44  thf('132', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | (r3_lattices @ sk_A @ 
% 8.21/8.44           (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)) @ 
% 8.21/8.44           (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['127', '131'])).
% 8.21/8.44  thf('133', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('134', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('135', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('136', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | (r3_lattices @ sk_A @ 
% 8.21/8.44           (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)) @ 
% 8.21/8.44           (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 8.21/8.44      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 8.21/8.44  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('138', plain,
% 8.21/8.44      ((r3_lattices @ sk_A @ 
% 8.21/8.44        (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)) @ 
% 8.21/8.44        (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))),
% 8.21/8.44      inference('clc', [status(thm)], ['136', '137'])).
% 8.21/8.44  thf('139', plain,
% 8.21/8.44      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A))),
% 8.21/8.44      inference('sup+', [status(thm)], ['2', '138'])).
% 8.21/8.44  thf('140', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('141', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('142', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('143', plain,
% 8.21/8.44      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))
% 8.21/8.44        | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 8.21/8.44  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('145', plain,
% 8.21/8.44      ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44        (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))),
% 8.21/8.44      inference('clc', [status(thm)], ['143', '144'])).
% 8.21/8.44  thf('146', plain,
% 8.21/8.44      ((r2_hidden @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['125', '126'])).
% 8.21/8.44  thf('147', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_3 @ X18 @ X17 @ X19) @ (u1_struct_0 @ X17))
% 8.21/8.44          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 8.21/8.44  thf('148', plain,
% 8.21/8.44      (((m1_subset_1 @ 
% 8.21/8.44         (sk_D_3 @ sk_B_1 @ sk_A @ 
% 8.21/8.44          (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)) @ 
% 8.21/8.44         (u1_struct_0 @ sk_A))
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['146', '147'])).
% 8.21/8.44  thf('149', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('150', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('151', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('152', plain,
% 8.21/8.44      (((m1_subset_1 @ 
% 8.21/8.44         (sk_D_3 @ sk_B_1 @ sk_A @ 
% 8.21/8.44          (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)) @ 
% 8.21/8.44         (u1_struct_0 @ sk_A))
% 8.21/8.44        | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 8.21/8.44  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('154', plain,
% 8.21/8.44      ((m1_subset_1 @ 
% 8.21/8.44        (sk_D_3 @ sk_B_1 @ sk_A @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)) @ 
% 8.21/8.44        (u1_struct_0 @ sk_A))),
% 8.21/8.44      inference('clc', [status(thm)], ['152', '153'])).
% 8.21/8.44  thf('155', plain,
% 8.21/8.44      ((r2_hidden @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['125', '126'])).
% 8.21/8.44  thf('156', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | ((X19) = (sk_D_3 @ X18 @ X17 @ X19))
% 8.21/8.44          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 8.21/8.44  thf('157', plain,
% 8.21/8.44      ((((sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)
% 8.21/8.44          = (sk_D_3 @ sk_B_1 @ sk_A @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A))),
% 8.21/8.44      inference('sup-', [status(thm)], ['155', '156'])).
% 8.21/8.44  thf('158', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('159', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('160', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('161', plain,
% 8.21/8.44      ((((sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)
% 8.21/8.44          = (sk_D_3 @ sk_B_1 @ sk_A @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))
% 8.21/8.44        | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 8.21/8.44  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('163', plain,
% 8.21/8.44      (((sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)
% 8.21/8.44         = (sk_D_3 @ sk_B_1 @ sk_A @ 
% 8.21/8.44            (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 8.21/8.44      inference('clc', [status(thm)], ['161', '162'])).
% 8.21/8.44  thf('164', plain,
% 8.21/8.44      ((m1_subset_1 @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44        (u1_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['154', '163'])).
% 8.21/8.44  thf('165', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('166', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf(d21_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44         ( ![B:$i,C:$i]:
% 8.21/8.44           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 8.21/8.44               ( ( r4_lattice3 @ A @ C @ B ) & 
% 8.21/8.44                 ( ![D:$i]:
% 8.21/8.44                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 8.21/8.44                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 8.21/8.44  thf('167', plain,
% 8.21/8.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X13)
% 8.21/8.44          | ~ (v10_lattices @ X13)
% 8.21/8.44          | ~ (v4_lattice3 @ X13)
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 8.21/8.44          | (r4_lattice3 @ X13 @ (sk_D_2 @ X14 @ X15 @ X13) @ X15)
% 8.21/8.44          | ((X14) = (k15_lattice3 @ X13 @ X15))
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | (v2_struct_0 @ X13))),
% 8.21/8.44      inference('cnf', [status(esa)], [d21_lattice3])).
% 8.21/8.44  thf('168', plain,
% 8.21/8.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.21/8.44         (((X14) = (k15_lattice3 @ X13 @ X15))
% 8.21/8.44          | (r4_lattice3 @ X13 @ (sk_D_2 @ X14 @ X15 @ X13) @ X15)
% 8.21/8.44          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 8.21/8.44          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | ~ (v4_lattice3 @ X13)
% 8.21/8.44          | ~ (v10_lattices @ X13)
% 8.21/8.44          | (v2_struct_0 @ X13))),
% 8.21/8.44      inference('simplify', [status(thm)], ['167'])).
% 8.21/8.44  thf('169', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['166', '168'])).
% 8.21/8.44  thf('170', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 8.21/8.44          | (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['169'])).
% 8.21/8.44  thf('171', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | (r4_lattice3 @ X1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 8.21/8.44          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['165', '170'])).
% 8.21/8.44  thf('172', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 8.21/8.44          | (r4_lattice3 @ X1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['171'])).
% 8.21/8.44  thf('173', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('174', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('175', plain,
% 8.21/8.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X13)
% 8.21/8.44          | ~ (v10_lattices @ X13)
% 8.21/8.44          | ~ (v4_lattice3 @ X13)
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_2 @ X14 @ X15 @ X13) @ (u1_struct_0 @ X13))
% 8.21/8.44          | ((X14) = (k15_lattice3 @ X13 @ X15))
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | (v2_struct_0 @ X13))),
% 8.21/8.44      inference('cnf', [status(esa)], [d21_lattice3])).
% 8.21/8.44  thf('176', plain,
% 8.21/8.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.21/8.44         (((X14) = (k15_lattice3 @ X13 @ X15))
% 8.21/8.44          | (m1_subset_1 @ (sk_D_2 @ X14 @ X15 @ X13) @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 8.21/8.44          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | ~ (v4_lattice3 @ X13)
% 8.21/8.44          | ~ (v10_lattices @ X13)
% 8.21/8.44          | (v2_struct_0 @ X13))),
% 8.21/8.44      inference('simplify', [status(thm)], ['175'])).
% 8.21/8.44  thf('177', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 8.21/8.44             (u1_struct_0 @ X0))
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['174', '176'])).
% 8.21/8.44  thf('178', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 8.21/8.44          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 8.21/8.44             (u1_struct_0 @ X0))
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['177'])).
% 8.21/8.44  thf('179', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 8.21/8.44             (u1_struct_0 @ X1))
% 8.21/8.44          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['173', '178'])).
% 8.21/8.44  thf('180', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 8.21/8.44          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 8.21/8.44             (u1_struct_0 @ X1))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['179'])).
% 8.21/8.44  thf('181', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | ~ (r4_lattice3 @ X10 @ X12 @ X11)
% 8.21/8.44          | (r1_lattices @ X10 @ (sk_C @ X11 @ X10) @ X12)
% 8.21/8.44          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('182', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 8.21/8.44             (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 8.21/8.44          | ~ (v4_lattice3 @ X0))),
% 8.21/8.44      inference('sup-', [status(thm)], ['180', '181'])).
% 8.21/8.44  thf('183', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (~ (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 8.21/8.44          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 8.21/8.44             (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['182'])).
% 8.21/8.44  thf('184', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 8.21/8.44          | (r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 8.21/8.44             (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['172', '183'])).
% 8.21/8.44  thf('185', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 8.21/8.44           (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1))
% 8.21/8.44          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['184'])).
% 8.21/8.44  thf('186', plain,
% 8.21/8.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X13)
% 8.21/8.44          | ~ (v10_lattices @ X13)
% 8.21/8.44          | ~ (v4_lattice3 @ X13)
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 8.21/8.44          | ~ (r1_lattices @ X13 @ X14 @ (sk_D_2 @ X14 @ X15 @ X13))
% 8.21/8.44          | ((X14) = (k15_lattice3 @ X13 @ X15))
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | (v2_struct_0 @ X13))),
% 8.21/8.44      inference('cnf', [status(esa)], [d21_lattice3])).
% 8.21/8.44  thf('187', plain,
% 8.21/8.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.21/8.44         (((X14) = (k15_lattice3 @ X13 @ X15))
% 8.21/8.44          | ~ (r1_lattices @ X13 @ X14 @ (sk_D_2 @ X14 @ X15 @ X13))
% 8.21/8.44          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 8.21/8.44          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 8.21/8.44          | ~ (l3_lattices @ X13)
% 8.21/8.44          | ~ (v4_lattice3 @ X13)
% 8.21/8.44          | ~ (v10_lattices @ X13)
% 8.21/8.44          | (v2_struct_0 @ X13))),
% 8.21/8.44      inference('simplify', [status(thm)], ['186'])).
% 8.21/8.44  thf('188', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 8.21/8.44          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['185', '187'])).
% 8.21/8.44  thf('189', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 8.21/8.44          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 8.21/8.44          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['188'])).
% 8.21/8.44  thf('190', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | ((sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)
% 8.21/8.44            = (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C_1)))
% 8.21/8.44        | ~ (r4_lattice3 @ sk_A @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44             (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['164', '189'])).
% 8.21/8.44  thf('191', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('192', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('193', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('194', plain,
% 8.21/8.44      ((m1_subset_1 @ (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44        (u1_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['154', '163'])).
% 8.21/8.44  thf(t43_lattice3, axiom,
% 8.21/8.44    (![A:$i]:
% 8.21/8.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 8.21/8.44         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 8.21/8.44       ( ![B:$i]:
% 8.21/8.44         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.21/8.44           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 8.21/8.44               ( B ) ) & 
% 8.21/8.44             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 8.21/8.44               ( B ) ) ) ) ) ))).
% 8.21/8.44  thf('195', plain,
% 8.21/8.44      (![X31 : $i, X32 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 8.21/8.44          | ((k16_lattice3 @ X32 @ (k6_domain_1 @ (u1_struct_0 @ X32) @ X31))
% 8.21/8.44              = (X31))
% 8.21/8.44          | ~ (l3_lattices @ X32)
% 8.21/8.44          | ~ (v4_lattice3 @ X32)
% 8.21/8.44          | ~ (v10_lattices @ X32)
% 8.21/8.44          | (v2_struct_0 @ X32))),
% 8.21/8.44      inference('cnf', [status(esa)], [t43_lattice3])).
% 8.21/8.44  thf('196', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A)
% 8.21/8.44        | ((k16_lattice3 @ sk_A @ 
% 8.21/8.44            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))
% 8.21/8.44            = (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['194', '195'])).
% 8.21/8.44  thf('197', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('198', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('199', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('200', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | ((k16_lattice3 @ sk_A @ 
% 8.21/8.44            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 8.21/8.44             (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))
% 8.21/8.44            = (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 8.21/8.44      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 8.21/8.44  thf('201', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('202', plain,
% 8.21/8.44      (((k16_lattice3 @ sk_A @ 
% 8.21/8.44         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 8.21/8.44          (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)))
% 8.21/8.44         = (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A))),
% 8.21/8.44      inference('clc', [status(thm)], ['200', '201'])).
% 8.21/8.44  thf('203', plain,
% 8.21/8.44      (![X10 : $i, X11 : $i]:
% 8.21/8.44         (~ (v4_lattice3 @ X10)
% 8.21/8.44          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 8.21/8.44          | ~ (l3_lattices @ X10)
% 8.21/8.44          | (v2_struct_0 @ X10))),
% 8.21/8.44      inference('cnf', [status(esa)], [d18_lattice3])).
% 8.21/8.44  thf('204', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.21/8.44         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 8.21/8.44          | (r2_hidden @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X2))
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['119'])).
% 8.21/8.44  thf('205', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | (r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0)))),
% 8.21/8.44      inference('sup-', [status(thm)], ['203', '204'])).
% 8.21/8.44  thf('206', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['205'])).
% 8.21/8.44  thf('207', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | ((X19) = (sk_D_3 @ X18 @ X17 @ X19))
% 8.21/8.44          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 8.21/8.44  thf('208', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['206', '207'])).
% 8.21/8.44  thf('209', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['208'])).
% 8.21/8.44  thf('210', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['205'])).
% 8.21/8.44  thf('211', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_3 @ X18 @ X17 @ X19) @ (u1_struct_0 @ X17))
% 8.21/8.44          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 8.21/8.44  thf('212', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | (m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 8.21/8.44             (u1_struct_0 @ X1))
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['210', '211'])).
% 8.21/8.44  thf('213', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 8.21/8.44           (u1_struct_0 @ X1))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['212'])).
% 8.21/8.44  thf('214', plain,
% 8.21/8.44      (![X31 : $i, X32 : $i]:
% 8.21/8.44         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 8.21/8.44          | ((k16_lattice3 @ X32 @ (k6_domain_1 @ (u1_struct_0 @ X32) @ X31))
% 8.21/8.44              = (X31))
% 8.21/8.44          | ~ (l3_lattices @ X32)
% 8.21/8.44          | ~ (v4_lattice3 @ X32)
% 8.21/8.44          | ~ (v10_lattices @ X32)
% 8.21/8.44          | (v2_struct_0 @ X32))),
% 8.21/8.44      inference('cnf', [status(esa)], [t43_lattice3])).
% 8.21/8.44  thf('215', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ((k16_lattice3 @ X0 @ 
% 8.21/8.44              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 8.21/8.44               (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0))))
% 8.21/8.44              = (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0))))),
% 8.21/8.44      inference('sup-', [status(thm)], ['213', '214'])).
% 8.21/8.44  thf('216', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k16_lattice3 @ X0 @ 
% 8.21/8.44            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 8.21/8.44             (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0))))
% 8.21/8.44            = (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)))
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0))),
% 8.21/8.44      inference('simplify', [status(thm)], ['215'])).
% 8.21/8.44  thf('217', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (((k16_lattice3 @ X0 @ 
% 8.21/8.44            (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_C @ X1 @ X0)))
% 8.21/8.44            = (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)))
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['209', '216'])).
% 8.21/8.44  thf('218', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ((k16_lattice3 @ X0 @ 
% 8.21/8.44              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_C @ X1 @ X0)))
% 8.21/8.44              = (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0))))),
% 8.21/8.44      inference('simplify', [status(thm)], ['217'])).
% 8.21/8.44  thf('219', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['205'])).
% 8.21/8.44  thf('220', plain,
% 8.21/8.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.21/8.44         (~ (l3_lattices @ X17)
% 8.21/8.44          | ~ (v4_lattice3 @ X17)
% 8.21/8.44          | ~ (v10_lattices @ X17)
% 8.21/8.44          | (v2_struct_0 @ X17)
% 8.21/8.44          | (r4_lattice3 @ X17 @ (sk_D_3 @ X18 @ X17 @ X19) @ X18)
% 8.21/8.44          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 8.21/8.44      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 8.21/8.44  thf('221', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((v2_struct_0 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | (r4_lattice3 @ X1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ X0)
% 8.21/8.44          | (v2_struct_0 @ X1)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1))),
% 8.21/8.44      inference('sup-', [status(thm)], ['219', '220'])).
% 8.21/8.44  thf('222', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r4_lattice3 @ X1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X1)
% 8.21/8.44          | ~ (v4_lattice3 @ X1)
% 8.21/8.44          | ~ (l3_lattices @ X1)
% 8.21/8.44          | (v2_struct_0 @ X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['221'])).
% 8.21/8.44  thf('223', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         ((r4_lattice3 @ X0 @ 
% 8.21/8.44           (k16_lattice3 @ X0 @ 
% 8.21/8.44            (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_C @ X1 @ X0))) @ 
% 8.21/8.44           X1)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (v10_lattices @ X0))),
% 8.21/8.44      inference('sup+', [status(thm)], ['218', '222'])).
% 8.21/8.44  thf('224', plain,
% 8.21/8.44      (![X0 : $i, X1 : $i]:
% 8.21/8.44         (~ (v10_lattices @ X0)
% 8.21/8.44          | ~ (v4_lattice3 @ X0)
% 8.21/8.44          | ~ (l3_lattices @ X0)
% 8.21/8.44          | (v2_struct_0 @ X0)
% 8.21/8.44          | (r4_lattice3 @ X0 @ 
% 8.21/8.44             (k16_lattice3 @ X0 @ 
% 8.21/8.44              (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_C @ X1 @ X0))) @ 
% 8.21/8.44             X1))),
% 8.21/8.44      inference('simplify', [status(thm)], ['223'])).
% 8.21/8.44  thf('225', plain,
% 8.21/8.44      (((r4_lattice3 @ sk_A @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44         (a_2_5_lattice3 @ sk_A @ sk_C_1))
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A))),
% 8.21/8.44      inference('sup+', [status(thm)], ['202', '224'])).
% 8.21/8.44  thf('226', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('227', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('228', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('229', plain,
% 8.21/8.44      (((r4_lattice3 @ sk_A @ 
% 8.21/8.44         (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44         (a_2_5_lattice3 @ sk_A @ sk_C_1))
% 8.21/8.44        | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 8.21/8.44  thf('230', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('231', plain,
% 8.21/8.44      ((r4_lattice3 @ sk_A @ 
% 8.21/8.44        (sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 8.21/8.44        (a_2_5_lattice3 @ sk_A @ sk_C_1))),
% 8.21/8.44      inference('clc', [status(thm)], ['229', '230'])).
% 8.21/8.44  thf('232', plain,
% 8.21/8.44      (((v2_struct_0 @ sk_A)
% 8.21/8.44        | ((sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)
% 8.21/8.44            = (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C_1))))),
% 8.21/8.44      inference('demod', [status(thm)], ['190', '191', '192', '193', '231'])).
% 8.21/8.44  thf('233', plain, (~ (v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('234', plain,
% 8.21/8.44      (((sk_C @ (a_2_5_lattice3 @ sk_A @ sk_C_1) @ sk_A)
% 8.21/8.44         = (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('clc', [status(thm)], ['232', '233'])).
% 8.21/8.44  thf('235', plain,
% 8.21/8.44      ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44        (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C_1)))),
% 8.21/8.44      inference('demod', [status(thm)], ['145', '234'])).
% 8.21/8.44  thf('236', plain,
% 8.21/8.44      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44         (k15_lattice3 @ sk_A @ sk_C_1))
% 8.21/8.44        | (v2_struct_0 @ sk_A)
% 8.21/8.44        | ~ (v10_lattices @ sk_A)
% 8.21/8.44        | ~ (v4_lattice3 @ sk_A)
% 8.21/8.44        | ~ (l3_lattices @ sk_A))),
% 8.21/8.44      inference('sup+', [status(thm)], ['1', '235'])).
% 8.21/8.44  thf('237', plain, ((v10_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('238', plain, ((v4_lattice3 @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('239', plain, ((l3_lattices @ sk_A)),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('240', plain,
% 8.21/8.44      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44         (k15_lattice3 @ sk_A @ sk_C_1))
% 8.21/8.44        | (v2_struct_0 @ sk_A))),
% 8.21/8.44      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 8.21/8.44  thf('241', plain,
% 8.21/8.44      (~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 8.21/8.44          (k15_lattice3 @ sk_A @ sk_C_1))),
% 8.21/8.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.21/8.44  thf('242', plain, ((v2_struct_0 @ sk_A)),
% 8.21/8.44      inference('clc', [status(thm)], ['240', '241'])).
% 8.21/8.44  thf('243', plain, ($false), inference('demod', [status(thm)], ['0', '242'])).
% 8.21/8.44  
% 8.21/8.44  % SZS output end Refutation
% 8.21/8.44  
% 8.21/8.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
