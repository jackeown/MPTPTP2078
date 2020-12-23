%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1159+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rwxbYbAOKc

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:11 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 492 expanded)
%              Number of leaves         :   24 ( 148 expanded)
%              Depth                    :   20
%              Number of atoms          :  903 (10511 expanded)
%              Number of equality atoms :   16 (  84 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t57_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                    <=> ( ( r2_orders_2 @ A @ B @ C )
                        & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_orders_2])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d14_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k3_orders_2 @ A @ B @ C )
                = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( ( k3_orders_2 @ X1 @ X0 @ X2 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_orders_2 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X2 ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_orders_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 )
        = ( k3_xboole_0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 )
        = ( k3_xboole_0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
      | ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf(t52_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ ( k2_orders_2 @ X13 @ ( k6_domain_1 @ ( u1_struct_0 @ X13 ) @ X14 ) ) )
      | ( r2_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_orders_2])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('40',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
      | ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['36','44','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_orders_2 @ X13 @ X12 @ X14 )
      | ( r2_hidden @ X12 @ ( k2_orders_2 @ X13 @ ( k6_domain_1 @ ( u1_struct_0 @ X13 ) @ X14 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_orders_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['36','44','45','59'])).

thf('61',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['65'])).

thf('71',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['36','44','45','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,(
    r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,
    ( ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('75',plain,(
    r2_hidden @ sk_B @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['47','75'])).


%------------------------------------------------------------------------------
