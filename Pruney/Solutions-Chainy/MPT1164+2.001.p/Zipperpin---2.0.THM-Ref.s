%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B5aftxF5Us

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 652 expanded)
%              Number of leaves         :   26 ( 199 expanded)
%              Depth                    :   26
%              Number of atoms          : 1040 (9996 expanded)
%              Number of equality atoms :   46 ( 128 expanded)
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

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
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
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
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
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_C_1
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
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

thf('51',plain,(
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

thf('52',plain,(
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
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf('75',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
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

thf('77',plain,(
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
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf('87',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['88','89'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['71','90','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B5aftxF5Us
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 76 iterations in 0.073s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.56  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.56  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.56  thf(t67_orders_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t67_orders_2])).
% 0.20/0.56  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d3_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X1 : $i, X3 : $i]:
% 0.20/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X1 : $i, X3 : $i]:
% 0.20/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('3', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_m1_orders_2, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( m1_orders_2 @ C @ A @ B ) =>
% 0.20/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (l1_orders_2 @ X14)
% 0.20/0.56          | ~ (v5_orders_2 @ X14)
% 0.20/0.56          | ~ (v4_orders_2 @ X14)
% 0.20/0.56          | ~ (v3_orders_2 @ X14)
% 0.20/0.56          | (v2_struct_0 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | ~ (m1_orders_2 @ X16 @ X14 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_orders_2])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.20/0.56  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.56  thf(t4_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.56          | (m1_subset_1 @ X7 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.56          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d15_orders_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.20/0.56                     ( ?[D:$i]:
% 0.20/0.56                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.20/0.56                         ( r2_hidden @ D @ B ) & 
% 0.20/0.56                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.20/0.56                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.20/0.56                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ((X10) = (k1_xboole_0))
% 0.20/0.56          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.20/0.56          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.20/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (l1_orders_2 @ X11)
% 0.20/0.56          | ~ (v5_orders_2 @ X11)
% 0.20/0.56          | ~ (v4_orders_2 @ X11)
% 0.20/0.56          | ~ (v3_orders_2 @ X11)
% 0.20/0.56          | (v2_struct_0 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.56          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.56          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.56        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '26'])).
% 0.20/0.56  thf('28', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.56          | (m1_subset_1 @ X7 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ((X10) = (k1_xboole_0))
% 0.20/0.56          | ((X12) = (k3_orders_2 @ X11 @ X10 @ (sk_D @ X12 @ X10 @ X11)))
% 0.20/0.56          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.20/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (l1_orders_2 @ X11)
% 0.20/0.56          | ~ (v5_orders_2 @ X11)
% 0.20/0.56          | ~ (v4_orders_2 @ X11)
% 0.20/0.56          | ~ (v3_orders_2 @ X11)
% 0.20/0.56          | (v2_struct_0 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.56          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.20/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.56          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.20/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | ((sk_C_1)
% 0.20/0.56            = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.20/0.56        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '44'])).
% 0.20/0.56  thf('46', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | ((sk_C_1)
% 0.20/0.56            = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      ((((sk_C_1) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.20/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t57_orders_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.20/0.56                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.56          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.20/0.56          | (r2_hidden @ X17 @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.20/0.56          | ~ (l1_orders_2 @ X18)
% 0.20/0.56          | ~ (v5_orders_2 @ X18)
% 0.20/0.56          | ~ (v4_orders_2 @ X18)
% 0.20/0.56          | ~ (v3_orders_2 @ X18)
% 0.20/0.56          | (v2_struct_0 @ X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X1 @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.56  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X1 @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.56          | ((sk_B) = (k1_xboole_0))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.56               (u1_struct_0 @ sk_A))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '57'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_B) = (k1_xboole_0))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | ((sk_B) = (k1_xboole_0))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '58'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.56          | ((sk_B) = (k1_xboole_0))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '60'])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.56          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | ((sk_B) = (k1_xboole_0))
% 0.20/0.56          | (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '61'])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_B) = (k1_xboole_0))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.20/0.56          | (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (![X1 : $i, X3 : $i]:
% 0.20/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | ((sk_B) = (k1_xboole_0))
% 0.20/0.56        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.20/0.56      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.56  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('68', plain, (((r1_tarski @ sk_C_1 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.56  thf('69', plain, (~ (r1_tarski @ sk_C_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('70', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf('71', plain, (~ (r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '70'])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('74', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ((X10) != (k1_xboole_0))
% 0.20/0.56          | ((X12) = (k1_xboole_0))
% 0.20/0.56          | ~ (m1_orders_2 @ X12 @ X11 @ X10)
% 0.20/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (l1_orders_2 @ X11)
% 0.20/0.56          | ~ (v5_orders_2 @ X11)
% 0.20/0.56          | ~ (v4_orders_2 @ X11)
% 0.20/0.56          | ~ (v3_orders_2 @ X11)
% 0.20/0.56          | (v2_struct_0 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X11)
% 0.20/0.56          | ~ (v3_orders_2 @ X11)
% 0.20/0.56          | ~ (v4_orders_2 @ X11)
% 0.20/0.56          | ~ (v5_orders_2 @ X11)
% 0.20/0.56          | ~ (l1_orders_2 @ X11)
% 0.20/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (m1_orders_2 @ X12 @ X11 @ k1_xboole_0)
% 0.20/0.56          | ((X12) = (k1_xboole_0))
% 0.20/0.56          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((X0) = (k1_xboole_0))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['75', '77'])).
% 0.20/0.56  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('80', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('81', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((X0) = (k1_xboole_0))
% 0.20/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ k1_xboole_0)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.20/0.56  thf('84', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0)
% 0.20/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['72', '83'])).
% 0.20/0.56  thf('85', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf('87', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ k1_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.56  thf('88', plain, (((v2_struct_0 @ sk_A) | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['84', '87'])).
% 0.20/0.56  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('90', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('92', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.56      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.56  thf('93', plain, ($false),
% 0.20/0.56      inference('demod', [status(thm)], ['71', '90', '92'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
