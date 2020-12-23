%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1561+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cCGD8qlixl

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:47 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 448 expanded)
%              Number of leaves         :   51 ( 149 expanded)
%              Depth                    :   29
%              Number of atoms          : 1693 (7246 expanded)
%              Number of equality atoms :   41 ( 353 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t39_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B )
            & ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                = B )
              & ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_yellow_0])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( ( k6_domain_1 @ X2 @ X3 )
        = ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B )
    | ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B )
   <= ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( ( k2_yellow_0 @ sk_A @ ( k1_tarski @ sk_B ) )
       != sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_lattice3 @ X13 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

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

thf('12',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( r2_lattice3 @ X43 @ ( k1_tarski @ X44 ) @ X42 )
      | ( r1_orders_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_orders_2 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X1 @ X4 @ X3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k1_tarski @ sk_B ) @ X3 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k1_tarski @ sk_B ) @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 ) ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_lattice3 @ X22 @ X25 @ X21 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X25 @ X21 @ X22 ) @ X25 @ X21 @ X22 )
      | ( zip_tseitin_2 @ X25 @ X21 @ X22 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( r1_orders_2 @ X43 @ X44 @ X42 )
      | ( r2_lattice3 @ X43 @ ( k1_tarski @ X44 ) @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_orders_2 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r3_orders_2 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r3_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['32','53'])).

thf('55',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('61',plain,
    ( ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['32','53'])).

thf('63',plain,
    ( ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X20
        = ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('66',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('68',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B )
   <= ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('69',plain,
    ( ( ( ( k1_yellow_0 @ sk_A @ ( k1_tarski @ sk_B ) )
       != sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['70'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('75',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B )
    | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('81',plain,(
    ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['6','81'])).

thf(t31_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) )
               => ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_3 @ D @ C @ B @ A ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_3 @ X26 @ X27 @ X28 @ X29 )
      | ( r1_lattice3 @ X29 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf(zf_stmt_9,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_3 @ D @ C @ B @ A ) )
     => ( zip_tseitin_4 @ D @ C @ B @ A ) ) )).

thf('84',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_4 @ X30 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_3 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_4 @ X30 @ X31 @ X32 @ X33 )
      | ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('88',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( r1_lattice3 @ X43 @ ( k1_tarski @ X44 ) @ X42 )
      | ( r1_orders_2 @ X43 @ X42 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_orders_2 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_4 @ X1 @ X4 @ X3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ~ ( r1_lattice3 @ X0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ X2 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( zip_tseitin_4 @ X0 @ X2 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_4 @ X0 @ ( k1_tarski @ sk_B ) @ X3 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ X2 @ X1 @ sk_A )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ X1 @ ( k1_tarski @ sk_B ) @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B ) ) ),
    inference(condensation,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_10,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( B
          = ( k2_yellow_0 @ A @ C ) )
        & ( r2_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_12,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_13,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_14,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_4 @ D @ C @ B @ A ) )
               => ( zip_tseitin_5 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k2_yellow_0 @ A @ C ) )
                  & ( r2_yellow_0 @ A @ C ) )
               => ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X37: $i,X38: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r1_lattice3 @ X38 @ X41 @ X37 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X41 @ X37 @ X38 ) @ X41 @ X37 @ X38 )
      | ( zip_tseitin_5 @ X41 @ X37 @ X38 )
      | ~ ( l1_orders_2 @ X38 )
      | ~ ( v5_orders_2 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_5 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( r1_orders_2 @ X43 @ X42 @ X44 )
      | ( r1_lattice3 @ X43 @ ( k1_tarski @ X44 ) @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_orders_2 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_yellow_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['51','52'])).

thf('110',plain,(
    r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['101','110'])).

thf('112',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_3 @ X26 @ X27 @ X28 @ X29 )
      | ~ ( r1_orders_2 @ X29 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_4 @ X30 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_3 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_4 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('117',plain,
    ( ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['108','109'])).

thf('119',plain,
    ( ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A )
    | ( zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    zip_tseitin_5 @ ( k1_tarski @ sk_B ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X36
        = ( k2_yellow_0 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_5 @ X35 @ X36 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('122',plain,
    ( sk_B
    = ( k2_yellow_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_B != sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','122'])).

thf('124',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('128',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).


%------------------------------------------------------------------------------
