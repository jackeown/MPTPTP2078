%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mf0Bvx28dG

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:05 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 634 expanded)
%              Number of leaves         :   25 ( 194 expanded)
%              Depth                    :   26
%              Number of atoms          : 1021 (9781 expanded)
%              Number of equality atoms :   43 ( 123 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t67_orders_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_orders_2 @ C @ A @ B )
               => ( r1_tarski @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_orders_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ sk_B ) ),
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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m1_orders_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_orders_2 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_orders_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d15_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( B != k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ? [D: $i] :
                        ( ( C
                          = ( k3_orders_2 @ A @ B @ D ) )
                        & ( r2_hidden @ D @ B )
                        & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) )
                & ( ( B = k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ( C = k1_xboole_0 ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_orders_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10 = k1_xboole_0 )
      | ( X12
        = ( k3_orders_2 @ X11 @ X10 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ~ ( m1_orders_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_1
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_orders_2 @ X18 @ X19 @ X20 ) )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['64','65'])).

thf('71',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10 != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_orders_2 @ X12 @ X11 @ k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['64','65'])).

thf('83',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['67','86','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mf0Bvx28dG
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 233 iterations in 0.210s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.66  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.46/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.66  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.46/0.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.66  thf(t67_orders_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.66            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t67_orders_2])).
% 0.46/0.66  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d3_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('3', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_m1_orders_2, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( ![C:$i]:
% 0.46/0.66         ( ( m1_orders_2 @ C @ A @ B ) =>
% 0.46/0.66           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.66         (~ (l1_orders_2 @ X14)
% 0.46/0.66          | ~ (v5_orders_2 @ X14)
% 0.46/0.66          | ~ (v4_orders_2 @ X14)
% 0.46/0.66          | ~ (v3_orders_2 @ X14)
% 0.46/0.66          | (v2_struct_0 @ X14)
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.66          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.66          | ~ (m1_orders_2 @ X16 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_m1_orders_2])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.46/0.66          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.46/0.66          | ~ (l1_orders_2 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.46/0.66          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.46/0.66  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '13'])).
% 0.46/0.66  thf(t4_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.66       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X7 @ X8)
% 0.46/0.66          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.46/0.66          | (m1_subset_1 @ X7 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_C_1 @ X0)
% 0.46/0.66          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '13'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d15_orders_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.66                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.46/0.66                     ( ?[D:$i]:
% 0.46/0.66                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.46/0.66                         ( r2_hidden @ D @ B ) & 
% 0.46/0.66                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.46/0.66                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.66                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.46/0.66                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ((X10) = (k1_xboole_0))
% 0.46/0.66          | (m1_subset_1 @ (sk_D @ X12 @ X10 @ X11) @ (u1_struct_0 @ X11))
% 0.46/0.66          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.46/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ~ (l1_orders_2 @ X11)
% 0.46/0.66          | ~ (v5_orders_2 @ X11)
% 0.46/0.66          | ~ (v4_orders_2 @ X11)
% 0.46/0.66          | ~ (v3_orders_2 @ X11)
% 0.46/0.66          | (v2_struct_0 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.46/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.46/0.66          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.46/0.66          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      ((((sk_B) = (k1_xboole_0))
% 0.46/0.66        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '26'])).
% 0.46/0.66  thf('28', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      ((((sk_B) = (k1_xboole_0))
% 0.46/0.66        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('clc', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '13'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ((X10) = (k1_xboole_0))
% 0.46/0.66          | ((X12) = (k3_orders_2 @ X11 @ X10 @ (sk_D @ X12 @ X10 @ X11)))
% 0.46/0.66          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.46/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ~ (l1_orders_2 @ X11)
% 0.46/0.66          | ~ (v5_orders_2 @ X11)
% 0.46/0.66          | ~ (v4_orders_2 @ X11)
% 0.46/0.66          | ~ (v3_orders_2 @ X11)
% 0.46/0.66          | (v2_struct_0 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.46/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.46/0.66          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.46/0.66          | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.46/0.66          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.46/0.66          | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((((sk_B) = (k1_xboole_0))
% 0.46/0.66        | ((sk_C_1)
% 0.46/0.66            = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.46/0.66        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['32', '40'])).
% 0.46/0.66  thf('42', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      ((((sk_B) = (k1_xboole_0))
% 0.46/0.66        | ((sk_C_1)
% 0.46/0.66            = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      ((((sk_C_1) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.46/0.66        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('clc', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t57_orders_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66               ( ![D:$i]:
% 0.46/0.66                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.46/0.66                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.46/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.66          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.46/0.66          | (r2_hidden @ X17 @ X19)
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.46/0.66          | ~ (l1_orders_2 @ X18)
% 0.46/0.66          | ~ (v5_orders_2 @ X18)
% 0.46/0.66          | ~ (v4_orders_2 @ X18)
% 0.46/0.66          | ~ (v3_orders_2 @ X18)
% 0.46/0.66          | (v2_struct_0 @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.46/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (r2_hidden @ X1 @ sk_B)
% 0.46/0.66          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.46/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain, ((v3_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain, ((v4_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('51', plain, ((v5_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (r2_hidden @ X1 @ sk_B)
% 0.46/0.66          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.46/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.46/0.66          | ((sk_B) = (k1_xboole_0))
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (r2_hidden @ X0 @ sk_B)
% 0.46/0.66          | ~ (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.46/0.66               (u1_struct_0 @ sk_A))
% 0.46/0.66          | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_B) = (k1_xboole_0))
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | (r2_hidden @ X0 @ sk_B)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ((sk_B) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (r2_hidden @ X0 @ sk_B)
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_C_1 @ X0)
% 0.46/0.66          | ((sk_B) = (k1_xboole_0))
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.46/0.66          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_C_1 @ X0)
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | ((sk_B) = (k1_xboole_0))
% 0.46/0.66          | (r1_tarski @ sk_C_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_B) = (k1_xboole_0))
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.46/0.66          | (r1_tarski @ sk_C_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ((sk_B) = (k1_xboole_0))
% 0.46/0.66        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      ((((sk_B) = (k1_xboole_0))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.46/0.66      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.66  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('64', plain, (((r1_tarski @ sk_C_1 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('clc', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('65', plain, (~ (r1_tarski @ sk_C_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('clc', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('67', plain, (~ (r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '13'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('70', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('clc', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ((X10) != (k1_xboole_0))
% 0.46/0.66          | ((X12) = (k1_xboole_0))
% 0.46/0.66          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.46/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ~ (l1_orders_2 @ X11)
% 0.46/0.66          | ~ (v5_orders_2 @ X11)
% 0.46/0.66          | ~ (v4_orders_2 @ X11)
% 0.46/0.66          | ~ (v3_orders_2 @ X11)
% 0.46/0.66          | (v2_struct_0 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         ((v2_struct_0 @ X11)
% 0.46/0.66          | ~ (v3_orders_2 @ X11)
% 0.46/0.66          | ~ (v4_orders_2 @ X11)
% 0.46/0.66          | ~ (v5_orders_2 @ X11)
% 0.46/0.66          | ~ (l1_orders_2 @ X11)
% 0.46/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ~ (m1_orders_2 @ X12 @ X11 @ k1_xboole_0)
% 0.46/0.66          | ((X12) = (k1_xboole_0))
% 0.46/0.66          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.46/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.46/0.66          | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['71', '73'])).
% 0.46/0.66  thf('75', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('77', plain, ((v4_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('78', plain, ((v3_orders_2 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0)
% 0.46/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['68', '79'])).
% 0.46/0.66  thf('81', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('82', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('clc', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('83', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.66  thf('84', plain, (((v2_struct_0 @ sk_A) | ((sk_C_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['80', '83'])).
% 0.46/0.66  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('86', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.66      inference('clc', [status(thm)], ['84', '85'])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.66  thf('90', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['89'])).
% 0.46/0.66  thf('91', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['67', '86', '90'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.50/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
