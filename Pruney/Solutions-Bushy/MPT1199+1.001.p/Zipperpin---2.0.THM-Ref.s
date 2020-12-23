%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1199+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eX5cfSz9Qa

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:14 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  605 (1900 expanded)
%              Number of equality atoms :   34 (  86 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(t26_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattices @ A @ B @ C )
                  & ( r1_lattices @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( l2_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_lattices @ A @ B @ C )
                    & ( r1_lattices @ A @ C @ B ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k1_lattices @ A @ B @ C )
                  = C ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_lattices @ X4 @ X3 @ X5 )
      | ( ( k1_lattices @ X4 @ X3 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_C @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_C @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_C @ sk_B )
    | ( ( k1_lattices @ sk_A @ sk_C @ sk_B )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_lattices @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ~ ( v4_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k3_lattices @ X7 @ X6 @ X8 )
        = ( k1_lattices @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C @ X0 )
        = ( k1_lattices @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v4_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C @ X0 )
        = ( k1_lattices @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C @ X0 )
        = ( k1_lattices @ sk_A @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_lattices @ sk_A @ sk_C @ sk_B )
    = ( k1_lattices @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k3_lattices @ A @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ~ ( v4_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k3_lattices @ X1 @ X0 @ X2 )
        = ( k3_lattices @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v4_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
    = ( k3_lattices @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
    = ( k1_lattices @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_lattices @ X4 @ X3 @ X5 )
      | ( ( k1_lattices @ X4 @ X3 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B @ sk_C )
    | ( ( k1_lattices @ sk_A @ sk_B @ sk_C )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r1_lattices @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ~ ( v4_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k3_lattices @ X7 @ X6 @ X8 )
        = ( k1_lattices @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v4_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
    = ( k1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,
    ( ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_C
    = ( k1_lattices @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['29','50'])).

thf('52',plain,
    ( ( sk_C = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','51'])).

thf('53',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).


%------------------------------------------------------------------------------
