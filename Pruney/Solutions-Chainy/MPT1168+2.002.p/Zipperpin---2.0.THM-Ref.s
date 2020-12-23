%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pUWeovZzAn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:08 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 596 expanded)
%              Number of leaves         :   26 ( 183 expanded)
%              Depth                    :   24
%              Number of atoms          : 2655 (14025 expanded)
%              Number of equality atoms :    6 ( 250 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t71_orders_2,conjecture,(
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
                 => ( ( ( r2_hidden @ B @ C )
                      & ( m1_orders_2 @ C @ A @ D ) )
                   => ( ( k3_orders_2 @ A @ C @ B )
                      = ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

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
                   => ( ( ( r2_hidden @ B @ C )
                        & ( m1_orders_2 @ C @ A @ D ) )
                     => ( ( k3_orders_2 @ A @ C @ B )
                        = ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_orders_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_orders_2 @ X19 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_C_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ( r2_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('51',plain,(
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
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(simplify,[status(thm)],['83'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
 != ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','103'])).

thf('105',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','103'])).

thf('122',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ( r2_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','103'])).

thf('139',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_orders_2,axiom,(
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
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( ( r2_orders_2 @ A @ B @ C )
                          & ( r2_hidden @ B @ D )
                          & ( r2_hidden @ C @ E )
                          & ( m1_orders_2 @ E @ A @ D ) )
                       => ( r2_hidden @ B @ E ) ) ) ) ) ) ) )).

thf('141',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r2_orders_2 @ X21 @ X20 @ X23 )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_orders_2 @ X24 @ X21 @ X22 )
      | ( r2_hidden @ X20 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_orders_2])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_orders_2 @ X1 @ sk_A @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_orders_2 @ X1 @ sk_A @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','147'])).

thf('149',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ~ ( r2_hidden @ sk_B @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','151'])).

thf('153',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','103'])).

thf('163',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('181',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['88','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pUWeovZzAn
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:59:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.96/2.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.96/2.15  % Solved by: fo/fo7.sh
% 1.96/2.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.15  % done 1165 iterations in 1.695s
% 1.96/2.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.96/2.15  % SZS output start Refutation
% 1.96/2.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.96/2.15  thf(sk_A_type, type, sk_A: $i).
% 1.96/2.15  thf(sk_D_type, type, sk_D: $i).
% 1.96/2.15  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 1.96/2.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.96/2.15  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.96/2.15  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.96/2.15  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 1.96/2.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.96/2.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.96/2.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.96/2.15  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.96/2.15  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.96/2.15  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.96/2.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.96/2.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.96/2.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.96/2.15  thf(sk_B_type, type, sk_B: $i).
% 1.96/2.15  thf(d3_tarski, axiom,
% 1.96/2.15    (![A:$i,B:$i]:
% 1.96/2.15     ( ( r1_tarski @ A @ B ) <=>
% 1.96/2.15       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.96/2.15  thf('0', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf(t71_orders_2, conjecture,
% 1.96/2.15    (![A:$i]:
% 1.96/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.96/2.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.96/2.15       ( ![B:$i]:
% 1.96/2.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.96/2.15           ( ![C:$i]:
% 1.96/2.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15               ( ![D:$i]:
% 1.96/2.15                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15                   ( ( ( r2_hidden @ B @ C ) & ( m1_orders_2 @ C @ A @ D ) ) =>
% 1.96/2.15                     ( ( k3_orders_2 @ A @ C @ B ) =
% 1.96/2.15                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 1.96/2.15  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.15    (~( ![A:$i]:
% 1.96/2.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.96/2.15            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.96/2.15          ( ![B:$i]:
% 1.96/2.15            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.96/2.15              ( ![C:$i]:
% 1.96/2.15                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15                  ( ![D:$i]:
% 1.96/2.15                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15                      ( ( ( r2_hidden @ B @ C ) & ( m1_orders_2 @ C @ A @ D ) ) =>
% 1.96/2.15                        ( ( k3_orders_2 @ A @ C @ B ) =
% 1.96/2.15                          ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 1.96/2.15    inference('cnf.neg', [status(esa)], [t71_orders_2])).
% 1.96/2.15  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('2', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf(dt_k3_orders_2, axiom,
% 1.96/2.15    (![A:$i,B:$i,C:$i]:
% 1.96/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.96/2.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.96/2.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.96/2.15         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15       ( m1_subset_1 @
% 1.96/2.15         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.96/2.15  thf('3', plain,
% 1.96/2.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.96/2.15          | ~ (l1_orders_2 @ X11)
% 1.96/2.15          | ~ (v5_orders_2 @ X11)
% 1.96/2.15          | ~ (v4_orders_2 @ X11)
% 1.96/2.15          | ~ (v3_orders_2 @ X11)
% 1.96/2.15          | (v2_struct_0 @ X11)
% 1.96/2.15          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 1.96/2.15          | (m1_subset_1 @ (k3_orders_2 @ X11 @ X10 @ X12) @ 
% 1.96/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 1.96/2.15      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 1.96/2.15  thf('4', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 1.96/2.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['2', '3'])).
% 1.96/2.15  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('9', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 1.96/2.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 1.96/2.15  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('11', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 1.96/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.96/2.15      inference('clc', [status(thm)], ['9', '10'])).
% 1.96/2.15  thf('12', plain,
% 1.96/2.15      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 1.96/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['1', '11'])).
% 1.96/2.15  thf(t4_subset, axiom,
% 1.96/2.15    (![A:$i,B:$i,C:$i]:
% 1.96/2.15     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.96/2.15       ( m1_subset_1 @ A @ C ) ))).
% 1.96/2.15  thf('13', plain,
% 1.96/2.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.96/2.15         (~ (r2_hidden @ X7 @ X8)
% 1.96/2.15          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.96/2.15          | (m1_subset_1 @ X7 @ X9))),
% 1.96/2.15      inference('cnf', [status(esa)], [t4_subset])).
% 1.96/2.15  thf('14', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['12', '13'])).
% 1.96/2.15  thf('15', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['0', '14'])).
% 1.96/2.15  thf('16', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('17', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf(t57_orders_2, axiom,
% 1.96/2.15    (![A:$i]:
% 1.96/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.96/2.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.96/2.15       ( ![B:$i]:
% 1.96/2.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.96/2.15           ( ![C:$i]:
% 1.96/2.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.96/2.15               ( ![D:$i]:
% 1.96/2.15                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 1.96/2.15                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.96/2.15  thf('18', plain,
% 1.96/2.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.96/2.15          | ~ (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 1.96/2.15          | (r2_hidden @ X13 @ X15)
% 1.96/2.15          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (l1_orders_2 @ X14)
% 1.96/2.15          | ~ (v5_orders_2 @ X14)
% 1.96/2.15          | ~ (v4_orders_2 @ X14)
% 1.96/2.15          | ~ (v3_orders_2 @ X14)
% 1.96/2.15          | (v2_struct_0 @ X14))),
% 1.96/2.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.96/2.15  thf('19', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['17', '18'])).
% 1.96/2.15  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('24', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.96/2.15  thf('25', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ X1)
% 1.96/2.15          | ~ (m1_subset_1 @ 
% 1.96/2.15               (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ 
% 1.96/2.15               (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['16', '24'])).
% 1.96/2.15  thf('26', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['15', '25'])).
% 1.96/2.15  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('28', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('demod', [status(thm)], ['26', '27'])).
% 1.96/2.15  thf('29', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15           sk_C_1)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['28'])).
% 1.96/2.15  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('31', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             sk_C_1))),
% 1.96/2.15      inference('clc', [status(thm)], ['29', '30'])).
% 1.96/2.15  thf('32', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('33', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf(t67_orders_2, axiom,
% 1.96/2.15    (![A:$i]:
% 1.96/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.96/2.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.96/2.15       ( ![B:$i]:
% 1.96/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 1.96/2.15  thf('34', plain,
% 1.96/2.15      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.96/2.15          | (r1_tarski @ X19 @ X17)
% 1.96/2.15          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 1.96/2.15          | ~ (l1_orders_2 @ X18)
% 1.96/2.15          | ~ (v5_orders_2 @ X18)
% 1.96/2.15          | ~ (v4_orders_2 @ X18)
% 1.96/2.15          | ~ (v3_orders_2 @ X18)
% 1.96/2.15          | (v2_struct_0 @ X18))),
% 1.96/2.15      inference('cnf', [status(esa)], [t67_orders_2])).
% 1.96/2.15  thf('35', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 1.96/2.15          | (r1_tarski @ X0 @ sk_D))),
% 1.96/2.15      inference('sup-', [status(thm)], ['33', '34'])).
% 1.96/2.15  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('40', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 1.96/2.15          | (r1_tarski @ X0 @ sk_D))),
% 1.96/2.15      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 1.96/2.15  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('42', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 1.96/2.15      inference('clc', [status(thm)], ['40', '41'])).
% 1.96/2.15  thf('43', plain, ((r1_tarski @ sk_C_1 @ sk_D)),
% 1.96/2.15      inference('sup-', [status(thm)], ['32', '42'])).
% 1.96/2.15  thf('44', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.15         (~ (r2_hidden @ X0 @ X1)
% 1.96/2.15          | (r2_hidden @ X0 @ X2)
% 1.96/2.15          | ~ (r1_tarski @ X1 @ X2))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('45', plain,
% 1.96/2.15      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.96/2.15      inference('sup-', [status(thm)], ['43', '44'])).
% 1.96/2.15  thf('46', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             sk_D))),
% 1.96/2.15      inference('sup-', [status(thm)], ['31', '45'])).
% 1.96/2.15  thf('47', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['0', '14'])).
% 1.96/2.15  thf('48', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('49', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('50', plain,
% 1.96/2.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.96/2.15          | ~ (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 1.96/2.15          | (r2_orders_2 @ X14 @ X13 @ X16)
% 1.96/2.15          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (l1_orders_2 @ X14)
% 1.96/2.15          | ~ (v5_orders_2 @ X14)
% 1.96/2.15          | ~ (v4_orders_2 @ X14)
% 1.96/2.15          | ~ (v3_orders_2 @ X14)
% 1.96/2.15          | (v2_struct_0 @ X14))),
% 1.96/2.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.96/2.15  thf('51', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['49', '50'])).
% 1.96/2.15  thf('52', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('54', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('56', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 1.96/2.15  thf('57', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ X1)
% 1.96/2.15          | ~ (m1_subset_1 @ 
% 1.96/2.15               (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ 
% 1.96/2.15               (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0)) @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['48', '56'])).
% 1.96/2.15  thf('58', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['47', '57'])).
% 1.96/2.15  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('60', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('demod', [status(thm)], ['58', '59'])).
% 1.96/2.15  thf('61', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r2_orders_2 @ sk_A @ 
% 1.96/2.15           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['60'])).
% 1.96/2.15  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('63', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B))),
% 1.96/2.15      inference('clc', [status(thm)], ['61', '62'])).
% 1.96/2.15  thf('64', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['0', '14'])).
% 1.96/2.15  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('66', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('67', plain,
% 1.96/2.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.96/2.15          | ~ (r2_orders_2 @ X14 @ X13 @ X16)
% 1.96/2.15          | ~ (r2_hidden @ X13 @ X15)
% 1.96/2.15          | (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 1.96/2.15          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (l1_orders_2 @ X14)
% 1.96/2.15          | ~ (v5_orders_2 @ X14)
% 1.96/2.15          | ~ (v4_orders_2 @ X14)
% 1.96/2.15          | ~ (v3_orders_2 @ X14)
% 1.96/2.15          | (v2_struct_0 @ X14))),
% 1.96/2.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.96/2.15  thf('68', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_D)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['66', '67'])).
% 1.96/2.15  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('70', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('71', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('73', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_D)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 1.96/2.15  thf('74', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 1.96/2.15          | ~ (r2_hidden @ X0 @ sk_D)
% 1.96/2.15          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['65', '73'])).
% 1.96/2.15  thf('75', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15          | ~ (r2_hidden @ 
% 1.96/2.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_D)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ 
% 1.96/2.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_B))),
% 1.96/2.15      inference('sup-', [status(thm)], ['64', '74'])).
% 1.96/2.15  thf('76', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | ~ (r2_hidden @ 
% 1.96/2.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_D)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['63', '75'])).
% 1.96/2.15  thf('77', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15          | ~ (r2_hidden @ 
% 1.96/2.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ sk_D)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['76'])).
% 1.96/2.15  thf('78', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['46', '77'])).
% 1.96/2.15  thf('79', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['78'])).
% 1.96/2.15  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('81', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 1.96/2.15      inference('clc', [status(thm)], ['79', '80'])).
% 1.96/2.15  thf('82', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('83', plain,
% 1.96/2.15      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 1.96/2.15         (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 1.96/2.15        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 1.96/2.15           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['81', '82'])).
% 1.96/2.15  thf('84', plain,
% 1.96/2.15      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 1.96/2.15        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 1.96/2.15      inference('simplify', [status(thm)], ['83'])).
% 1.96/2.15  thf(d10_xboole_0, axiom,
% 1.96/2.15    (![A:$i,B:$i]:
% 1.96/2.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.96/2.15  thf('85', plain,
% 1.96/2.15      (![X4 : $i, X6 : $i]:
% 1.96/2.15         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.96/2.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.15  thf('86', plain,
% 1.96/2.15      ((~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.96/2.15           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 1.96/2.15            = (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['84', '85'])).
% 1.96/2.15  thf('87', plain,
% 1.96/2.15      (((k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 1.96/2.15         != (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('88', plain,
% 1.96/2.15      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.96/2.15          (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 1.96/2.15      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 1.96/2.15  thf('89', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('90', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('91', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('92', plain,
% 1.96/2.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.96/2.15          | ~ (l1_orders_2 @ X11)
% 1.96/2.15          | ~ (v5_orders_2 @ X11)
% 1.96/2.15          | ~ (v4_orders_2 @ X11)
% 1.96/2.15          | ~ (v3_orders_2 @ X11)
% 1.96/2.15          | (v2_struct_0 @ X11)
% 1.96/2.15          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 1.96/2.15          | (m1_subset_1 @ (k3_orders_2 @ X11 @ X10 @ X12) @ 
% 1.96/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 1.96/2.15      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 1.96/2.15  thf('93', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 1.96/2.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['91', '92'])).
% 1.96/2.15  thf('94', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('95', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('98', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 1.96/2.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 1.96/2.15  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('100', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 1.96/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.96/2.15      inference('clc', [status(thm)], ['98', '99'])).
% 1.96/2.15  thf('101', plain,
% 1.96/2.15      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.96/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['90', '100'])).
% 1.96/2.15  thf('102', plain,
% 1.96/2.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.96/2.15         (~ (r2_hidden @ X7 @ X8)
% 1.96/2.15          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.96/2.15          | (m1_subset_1 @ X7 @ X9))),
% 1.96/2.15      inference('cnf', [status(esa)], [t4_subset])).
% 1.96/2.15  thf('103', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['101', '102'])).
% 1.96/2.15  thf('104', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['89', '103'])).
% 1.96/2.15  thf('105', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('106', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('107', plain,
% 1.96/2.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.96/2.15          | ~ (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 1.96/2.15          | (r2_hidden @ X13 @ X15)
% 1.96/2.15          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (l1_orders_2 @ X14)
% 1.96/2.15          | ~ (v5_orders_2 @ X14)
% 1.96/2.15          | ~ (v4_orders_2 @ X14)
% 1.96/2.15          | ~ (v3_orders_2 @ X14)
% 1.96/2.15          | (v2_struct_0 @ X14))),
% 1.96/2.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.96/2.15  thf('108', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ sk_D)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['106', '107'])).
% 1.96/2.15  thf('109', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('110', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('111', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('112', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('113', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ sk_D)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 1.96/2.15  thf('114', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 1.96/2.15          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 1.96/2.15               (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ sk_D)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['105', '113'])).
% 1.96/2.15  thf('115', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_D)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['104', '114'])).
% 1.96/2.15  thf('116', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('117', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_D)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('demod', [status(thm)], ['115', '116'])).
% 1.96/2.15  thf('118', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_D)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['117'])).
% 1.96/2.15  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('120', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_D))),
% 1.96/2.15      inference('clc', [status(thm)], ['118', '119'])).
% 1.96/2.15  thf('121', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['89', '103'])).
% 1.96/2.15  thf('122', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('123', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('124', plain,
% 1.96/2.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.96/2.15          | ~ (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 1.96/2.15          | (r2_orders_2 @ X14 @ X13 @ X16)
% 1.96/2.15          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (l1_orders_2 @ X14)
% 1.96/2.15          | ~ (v5_orders_2 @ X14)
% 1.96/2.15          | ~ (v4_orders_2 @ X14)
% 1.96/2.15          | ~ (v3_orders_2 @ X14)
% 1.96/2.15          | (v2_struct_0 @ X14))),
% 1.96/2.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.96/2.15  thf('125', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['123', '124'])).
% 1.96/2.15  thf('126', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('127', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('128', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('129', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('130', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 1.96/2.15  thf('131', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 1.96/2.15          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 1.96/2.15               (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['122', '130'])).
% 1.96/2.15  thf('132', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['121', '131'])).
% 1.96/2.15  thf('133', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('134', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('demod', [status(thm)], ['132', '133'])).
% 1.96/2.15  thf('135', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r2_orders_2 @ sk_A @ 
% 1.96/2.15           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['134'])).
% 1.96/2.15  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('137', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B))),
% 1.96/2.15      inference('clc', [status(thm)], ['135', '136'])).
% 1.96/2.15  thf('138', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['89', '103'])).
% 1.96/2.15  thf('139', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('140', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf(t70_orders_2, axiom,
% 1.96/2.15    (![A:$i]:
% 1.96/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.96/2.15         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.96/2.15       ( ![B:$i]:
% 1.96/2.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.96/2.15           ( ![C:$i]:
% 1.96/2.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.96/2.15               ( ![D:$i]:
% 1.96/2.15                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15                   ( ![E:$i]:
% 1.96/2.15                     ( ( m1_subset_1 @
% 1.96/2.15                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.15                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 1.96/2.15                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 1.96/2.15                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 1.96/2.15                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.96/2.15  thf('141', plain,
% 1.96/2.15      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.96/2.15          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.96/2.15          | ~ (r2_orders_2 @ X21 @ X20 @ X23)
% 1.96/2.15          | ~ (r2_hidden @ X20 @ X22)
% 1.96/2.15          | ~ (r2_hidden @ X23 @ X24)
% 1.96/2.15          | ~ (m1_orders_2 @ X24 @ X21 @ X22)
% 1.96/2.15          | (r2_hidden @ X20 @ X24)
% 1.96/2.15          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.96/2.15          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 1.96/2.15          | ~ (l1_orders_2 @ X21)
% 1.96/2.15          | ~ (v5_orders_2 @ X21)
% 1.96/2.15          | ~ (v4_orders_2 @ X21)
% 1.96/2.15          | ~ (v3_orders_2 @ X21)
% 1.96/2.15          | (v2_struct_0 @ X21))),
% 1.96/2.15      inference('cnf', [status(esa)], [t70_orders_2])).
% 1.96/2.15  thf('142', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.96/2.15          | (r2_hidden @ X2 @ X1)
% 1.96/2.15          | ~ (m1_orders_2 @ X1 @ sk_A @ sk_D)
% 1.96/2.15          | ~ (r2_hidden @ X0 @ X1)
% 1.96/2.15          | ~ (r2_hidden @ X2 @ sk_D)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X2 @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['140', '141'])).
% 1.96/2.15  thf('143', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('144', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('145', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('146', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('147', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.96/2.15          | (r2_hidden @ X2 @ X1)
% 1.96/2.15          | ~ (m1_orders_2 @ X1 @ sk_A @ sk_D)
% 1.96/2.15          | ~ (r2_hidden @ X0 @ X1)
% 1.96/2.15          | ~ (r2_hidden @ X2 @ sk_D)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X2 @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 1.96/2.15  thf('148', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 1.96/2.15          | ~ (r2_hidden @ X0 @ sk_D)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 1.96/2.15          | (r2_hidden @ X0 @ sk_C_1)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['139', '147'])).
% 1.96/2.15  thf('149', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('150', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 1.96/2.15          | ~ (r2_hidden @ X0 @ sk_D)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | (r2_hidden @ X0 @ sk_C_1)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('demod', [status(thm)], ['148', '149'])).
% 1.96/2.15  thf('151', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_D)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ 
% 1.96/2.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1))),
% 1.96/2.15      inference('sup-', [status(thm)], ['138', '150'])).
% 1.96/2.15  thf('152', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_D)
% 1.96/2.15          | ~ (r2_hidden @ sk_B @ sk_C_1)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['137', '151'])).
% 1.96/2.15  thf('153', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('154', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('155', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_D)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.96/2.15  thf('156', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_D)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['155'])).
% 1.96/2.15  thf('157', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['120', '156'])).
% 1.96/2.15  thf('158', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['157'])).
% 1.96/2.15  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('160', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             sk_C_1))),
% 1.96/2.15      inference('clc', [status(thm)], ['158', '159'])).
% 1.96/2.15  thf('161', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_orders_2 @ sk_A @ 
% 1.96/2.15             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B))),
% 1.96/2.15      inference('clc', [status(thm)], ['135', '136'])).
% 1.96/2.15  thf('162', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['89', '103'])).
% 1.96/2.15  thf('163', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('164', plain,
% 1.96/2.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('165', plain,
% 1.96/2.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.96/2.15          | ~ (r2_orders_2 @ X14 @ X13 @ X16)
% 1.96/2.15          | ~ (r2_hidden @ X13 @ X15)
% 1.96/2.15          | (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 1.96/2.15          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.96/2.15          | ~ (l1_orders_2 @ X14)
% 1.96/2.15          | ~ (v5_orders_2 @ X14)
% 1.96/2.15          | ~ (v4_orders_2 @ X14)
% 1.96/2.15          | ~ (v3_orders_2 @ X14)
% 1.96/2.15          | (v2_struct_0 @ X14))),
% 1.96/2.15      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.96/2.15  thf('166', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (v3_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v4_orders_2 @ sk_A)
% 1.96/2.15          | ~ (v5_orders_2 @ sk_A)
% 1.96/2.15          | ~ (l1_orders_2 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['164', '165'])).
% 1.96/2.15  thf('167', plain, ((v3_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('168', plain, ((v4_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('169', plain, ((v5_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('170', plain, ((l1_orders_2 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('171', plain,
% 1.96/2.15      (![X0 : $i, X1 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 1.96/2.15          | ~ (r2_hidden @ X1 @ sk_C_1)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 1.96/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.96/2.15      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 1.96/2.15  thf('172', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 1.96/2.15          | ~ (r2_hidden @ X0 @ sk_C_1)
% 1.96/2.15          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['163', '171'])).
% 1.96/2.15  thf('173', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_C_1)
% 1.96/2.15          | ~ (r2_orders_2 @ sk_A @ 
% 1.96/2.15               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B))),
% 1.96/2.15      inference('sup-', [status(thm)], ['162', '172'])).
% 1.96/2.15  thf('174', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_C_1)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15          | (v2_struct_0 @ sk_A)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('sup-', [status(thm)], ['161', '173'])).
% 1.96/2.15  thf('175', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15               sk_C_1)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['174'])).
% 1.96/2.15  thf('176', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15          | (v2_struct_0 @ sk_A))),
% 1.96/2.15      inference('sup-', [status(thm)], ['160', '175'])).
% 1.96/2.15  thf('177', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((v2_struct_0 @ sk_A)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 1.96/2.15      inference('simplify', [status(thm)], ['176'])).
% 1.96/2.15  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.15  thf('179', plain,
% 1.96/2.15      (![X0 : $i]:
% 1.96/2.15         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.96/2.15          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.96/2.15             (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 1.96/2.15      inference('clc', [status(thm)], ['177', '178'])).
% 1.96/2.15  thf('180', plain,
% 1.96/2.15      (![X1 : $i, X3 : $i]:
% 1.96/2.15         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.96/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.15  thf('181', plain,
% 1.96/2.15      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.96/2.15         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 1.96/2.15        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.96/2.15           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 1.96/2.15      inference('sup-', [status(thm)], ['179', '180'])).
% 1.96/2.15  thf('182', plain,
% 1.96/2.15      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.96/2.15        (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 1.96/2.15      inference('simplify', [status(thm)], ['181'])).
% 1.96/2.15  thf('183', plain, ($false), inference('demod', [status(thm)], ['88', '182'])).
% 1.96/2.15  
% 1.96/2.15  % SZS output end Refutation
% 1.96/2.15  
% 1.96/2.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
