%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TuqGSxP8Ri

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:04 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 227 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          : 1123 (4679 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t65_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r1_tarski @ C @ D )
                   => ( r1_tarski @ ( k3_orders_2 @ A @ C @ B ) @ ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

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
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( r1_tarski @ C @ D )
                     => ( r1_tarski @ ( k3_orders_2 @ A @ C @ B ) @ ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_orders_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_orders_2,axiom,(
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

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TuqGSxP8Ri
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.94/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.94/1.15  % Solved by: fo/fo7.sh
% 0.94/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.94/1.15  % done 626 iterations in 0.695s
% 0.94/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.94/1.15  % SZS output start Refutation
% 0.94/1.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.94/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.94/1.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.94/1.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.94/1.15  thf(sk_D_type, type, sk_D: $i).
% 0.94/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.94/1.15  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.94/1.15  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.94/1.15  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.94/1.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.94/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.94/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.94/1.15  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.94/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.94/1.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.94/1.15  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.94/1.15  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.94/1.15  thf(t65_orders_2, conjecture,
% 0.94/1.15    (![A:$i]:
% 0.94/1.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.94/1.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.94/1.15       ( ![B:$i]:
% 0.94/1.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.94/1.15           ( ![C:$i]:
% 0.94/1.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.94/1.15               ( ![D:$i]:
% 0.94/1.15                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.94/1.15                   ( ( r1_tarski @ C @ D ) =>
% 0.94/1.15                     ( r1_tarski @
% 0.94/1.15                       ( k3_orders_2 @ A @ C @ B ) @ 
% 0.94/1.15                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.94/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.94/1.15    (~( ![A:$i]:
% 0.94/1.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.94/1.15            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.94/1.15          ( ![B:$i]:
% 0.94/1.15            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.94/1.15              ( ![C:$i]:
% 0.94/1.15                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.94/1.15                  ( ![D:$i]:
% 0.94/1.15                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.94/1.15                      ( ( r1_tarski @ C @ D ) =>
% 0.94/1.15                        ( r1_tarski @
% 0.94/1.15                          ( k3_orders_2 @ A @ C @ B ) @ 
% 0.94/1.15                          ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.94/1.15    inference('cnf.neg', [status(esa)], [t65_orders_2])).
% 0.94/1.15  thf('0', plain,
% 0.94/1.15      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.94/1.15          (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(d3_tarski, axiom,
% 0.94/1.15    (![A:$i,B:$i]:
% 0.94/1.15     ( ( r1_tarski @ A @ B ) <=>
% 0.94/1.15       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.94/1.15  thf('1', plain,
% 0.94/1.15      (![X1 : $i, X3 : $i]:
% 0.94/1.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.94/1.15      inference('cnf', [status(esa)], [d3_tarski])).
% 0.94/1.15  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('3', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(dt_k3_orders_2, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.94/1.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.94/1.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.94/1.15         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.94/1.15       ( m1_subset_1 @
% 0.94/1.15         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.94/1.15  thf('4', plain,
% 0.94/1.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.94/1.15         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.94/1.15          | ~ (l1_orders_2 @ X8)
% 0.94/1.15          | ~ (v5_orders_2 @ X8)
% 0.94/1.15          | ~ (v4_orders_2 @ X8)
% 0.94/1.15          | ~ (v3_orders_2 @ X8)
% 0.94/1.15          | (v2_struct_0 @ X8)
% 0.94/1.15          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.94/1.15          | (m1_subset_1 @ (k3_orders_2 @ X8 @ X7 @ X9) @ 
% 0.94/1.15             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.94/1.15      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.94/1.15  thf('5', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 0.94/1.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (v3_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v4_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v5_orders_2 @ sk_A)
% 0.94/1.15          | ~ (l1_orders_2 @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['3', '4'])).
% 0.94/1.15  thf('6', plain, ((v3_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('7', plain, ((v4_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('8', plain, ((v5_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('10', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 0.94/1.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (v2_struct_0 @ sk_A))),
% 0.94/1.15      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.94/1.15  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('12', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 0.94/1.15             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.94/1.15      inference('clc', [status(thm)], ['10', '11'])).
% 0.94/1.15  thf('13', plain,
% 0.94/1.15      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.94/1.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['2', '12'])).
% 0.94/1.15  thf(t4_subset, axiom,
% 0.94/1.15    (![A:$i,B:$i,C:$i]:
% 0.94/1.15     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.94/1.15       ( m1_subset_1 @ A @ C ) ))).
% 0.94/1.15  thf('14', plain,
% 0.94/1.15      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.94/1.15         (~ (r2_hidden @ X4 @ X5)
% 0.94/1.15          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.94/1.15          | (m1_subset_1 @ X4 @ X6))),
% 0.94/1.15      inference('cnf', [status(esa)], [t4_subset])).
% 0.94/1.15  thf('15', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['13', '14'])).
% 0.94/1.15  thf('16', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (m1_subset_1 @ 
% 0.94/1.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['1', '15'])).
% 0.94/1.15  thf('17', plain,
% 0.94/1.15      (![X1 : $i, X3 : $i]:
% 0.94/1.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.94/1.15      inference('cnf', [status(esa)], [d3_tarski])).
% 0.94/1.15  thf('18', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf(t57_orders_2, axiom,
% 0.94/1.15    (![A:$i]:
% 0.94/1.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.94/1.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.94/1.15       ( ![B:$i]:
% 0.94/1.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.94/1.15           ( ![C:$i]:
% 0.94/1.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.94/1.15               ( ![D:$i]:
% 0.94/1.15                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.94/1.15                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.94/1.15                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.94/1.15  thf('19', plain,
% 0.94/1.15      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.94/1.15         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.94/1.15          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.94/1.15          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 0.94/1.15          | (r2_hidden @ X10 @ X12)
% 0.94/1.15          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.94/1.15          | ~ (l1_orders_2 @ X11)
% 0.94/1.15          | ~ (v5_orders_2 @ X11)
% 0.94/1.15          | ~ (v4_orders_2 @ X11)
% 0.94/1.15          | ~ (v3_orders_2 @ X11)
% 0.94/1.15          | (v2_struct_0 @ X11))),
% 0.94/1.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.94/1.15  thf('20', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (v3_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v4_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v5_orders_2 @ sk_A)
% 0.94/1.15          | ~ (l1_orders_2 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_hidden @ X1 @ sk_C_1)
% 0.94/1.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 0.94/1.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['18', '19'])).
% 0.94/1.15  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('25', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_hidden @ X1 @ sk_C_1)
% 0.94/1.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 0.94/1.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.94/1.15  thf('26', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.94/1.15          | ~ (m1_subset_1 @ 
% 0.94/1.15               (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ 
% 0.94/1.15               (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_hidden @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ 
% 0.94/1.15             sk_C_1)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (v2_struct_0 @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['17', '25'])).
% 0.94/1.15  thf('27', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             sk_C_1)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('sup-', [status(thm)], ['16', '26'])).
% 0.94/1.15  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('29', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             sk_C_1)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('demod', [status(thm)], ['27', '28'])).
% 0.94/1.15  thf('30', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15           sk_C_1)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('simplify', [status(thm)], ['29'])).
% 0.94/1.15  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('32', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             sk_C_1))),
% 0.94/1.15      inference('clc', [status(thm)], ['30', '31'])).
% 0.94/1.15  thf('33', plain, ((r1_tarski @ sk_C_1 @ sk_D)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('34', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.15         (~ (r2_hidden @ X0 @ X1)
% 0.94/1.15          | (r2_hidden @ X0 @ X2)
% 0.94/1.15          | ~ (r1_tarski @ X1 @ X2))),
% 0.94/1.15      inference('cnf', [status(esa)], [d3_tarski])).
% 0.94/1.15  thf('35', plain,
% 0.94/1.15      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.94/1.15      inference('sup-', [status(thm)], ['33', '34'])).
% 0.94/1.15  thf('36', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             sk_D))),
% 0.94/1.15      inference('sup-', [status(thm)], ['32', '35'])).
% 0.94/1.15  thf('37', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (m1_subset_1 @ 
% 0.94/1.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['1', '15'])).
% 0.94/1.15  thf('38', plain,
% 0.94/1.15      (![X1 : $i, X3 : $i]:
% 0.94/1.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.94/1.15      inference('cnf', [status(esa)], [d3_tarski])).
% 0.94/1.15  thf('39', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('40', plain,
% 0.94/1.15      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.94/1.15         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.94/1.15          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.94/1.15          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 0.94/1.15          | (r2_orders_2 @ X11 @ X10 @ X13)
% 0.94/1.15          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.94/1.15          | ~ (l1_orders_2 @ X11)
% 0.94/1.15          | ~ (v5_orders_2 @ X11)
% 0.94/1.15          | ~ (v4_orders_2 @ X11)
% 0.94/1.15          | ~ (v3_orders_2 @ X11)
% 0.94/1.15          | (v2_struct_0 @ X11))),
% 0.94/1.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.94/1.15  thf('41', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (v3_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v4_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v5_orders_2 @ sk_A)
% 0.94/1.15          | ~ (l1_orders_2 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.94/1.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 0.94/1.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['39', '40'])).
% 0.94/1.15  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('46', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.94/1.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 0.94/1.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.94/1.15  thf('47', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.94/1.15          | ~ (m1_subset_1 @ 
% 0.94/1.15               (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ 
% 0.94/1.15               (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_orders_2 @ sk_A @ 
% 0.94/1.15             (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ X0)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (v2_struct_0 @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['38', '46'])).
% 0.94/1.15  thf('48', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_orders_2 @ sk_A @ 
% 0.94/1.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('sup-', [status(thm)], ['37', '47'])).
% 0.94/1.15  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('50', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | (r2_orders_2 @ sk_A @ 
% 0.94/1.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('demod', [status(thm)], ['48', '49'])).
% 0.94/1.15  thf('51', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r2_orders_2 @ sk_A @ 
% 0.94/1.15           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('simplify', [status(thm)], ['50'])).
% 0.94/1.15  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('53', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (r2_orders_2 @ sk_A @ 
% 0.94/1.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B))),
% 0.94/1.15      inference('clc', [status(thm)], ['51', '52'])).
% 0.94/1.15  thf('54', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (m1_subset_1 @ 
% 0.94/1.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['1', '15'])).
% 0.94/1.15  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('56', plain,
% 0.94/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('57', plain,
% 0.94/1.15      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.94/1.15         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.94/1.15          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.94/1.15          | ~ (r2_orders_2 @ X11 @ X10 @ X13)
% 0.94/1.15          | ~ (r2_hidden @ X10 @ X12)
% 0.94/1.15          | (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 0.94/1.15          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.94/1.15          | ~ (l1_orders_2 @ X11)
% 0.94/1.15          | ~ (v5_orders_2 @ X11)
% 0.94/1.15          | ~ (v4_orders_2 @ X11)
% 0.94/1.15          | ~ (v3_orders_2 @ X11)
% 0.94/1.15          | (v2_struct_0 @ X11))),
% 0.94/1.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.94/1.15  thf('58', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (v3_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v4_orders_2 @ sk_A)
% 0.94/1.15          | ~ (v5_orders_2 @ sk_A)
% 0.94/1.15          | ~ (l1_orders_2 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.94/1.15          | ~ (r2_hidden @ X1 @ sk_D)
% 0.94/1.15          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.94/1.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['56', '57'])).
% 0.94/1.15  thf('59', plain, ((v3_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('60', plain, ((v4_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('61', plain, ((v5_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('63', plain,
% 0.94/1.15      (![X0 : $i, X1 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.94/1.15          | ~ (r2_hidden @ X1 @ sk_D)
% 0.94/1.15          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.94/1.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.94/1.15      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.94/1.15  thf('64', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.94/1.15          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 0.94/1.15          | ~ (r2_hidden @ X0 @ sk_D)
% 0.94/1.15          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15          | (v2_struct_0 @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['55', '63'])).
% 0.94/1.15  thf('65', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15          | ~ (r2_hidden @ 
% 0.94/1.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_D)
% 0.94/1.15          | ~ (r2_orders_2 @ sk_A @ 
% 0.94/1.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B))),
% 0.94/1.15      inference('sup-', [status(thm)], ['54', '64'])).
% 0.94/1.15  thf('66', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | ~ (r2_hidden @ 
% 0.94/1.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_D)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15          | (v2_struct_0 @ sk_A)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('sup-', [status(thm)], ['53', '65'])).
% 0.94/1.15  thf('67', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15          | ~ (r2_hidden @ 
% 0.94/1.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_D)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('simplify', [status(thm)], ['66'])).
% 0.94/1.15  thf('68', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15          | (v2_struct_0 @ sk_A))),
% 0.94/1.15      inference('sup-', [status(thm)], ['36', '67'])).
% 0.94/1.15  thf('69', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((v2_struct_0 @ sk_A)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 0.94/1.15      inference('simplify', [status(thm)], ['68'])).
% 0.94/1.15  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.94/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.15  thf('71', plain,
% 0.94/1.15      (![X0 : $i]:
% 0.94/1.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 0.94/1.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 0.94/1.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.94/1.15      inference('clc', [status(thm)], ['69', '70'])).
% 0.94/1.15  thf('72', plain,
% 0.94/1.15      (![X1 : $i, X3 : $i]:
% 0.94/1.15         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.94/1.15      inference('cnf', [status(esa)], [d3_tarski])).
% 0.94/1.15  thf('73', plain,
% 0.94/1.15      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.94/1.15         (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 0.94/1.15        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.94/1.15           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.94/1.15      inference('sup-', [status(thm)], ['71', '72'])).
% 0.94/1.15  thf('74', plain,
% 0.94/1.15      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 0.94/1.15        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.94/1.15      inference('simplify', [status(thm)], ['73'])).
% 0.94/1.15  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.94/1.15  
% 0.94/1.15  % SZS output end Refutation
% 0.94/1.15  
% 0.98/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
