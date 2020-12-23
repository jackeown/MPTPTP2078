%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KeqLafdl1A

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:08 EST 2020

% Result     : Theorem 50.35s
% Output     : Refutation 50.35s
% Verified   : 
% Statistics : Number of formulae       :  330 (3587 expanded)
%              Number of leaves         :   27 (1031 expanded)
%              Depth                    :   45
%              Number of atoms          : 4866 (91037 expanded)
%              Number of equality atoms :    7 (1674 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','47'])).

thf('49',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('53',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('72',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( r2_orders_2 @ X27 @ X26 @ X29 )
      | ~ ( r2_hidden @ X26 @ X28 )
      | ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( m1_orders_2 @ X30 @ X27 @ X28 )
      | ( r2_hidden @ X26 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_orders_2])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_orders_2 @ X1 @ sk_A @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_orders_2 @ X1 @ sk_A @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','84'])).

thf('86',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('97',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['97'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('103',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('109',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('120',plain,(
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
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['116','126'])).

thf('128',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('135',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('139',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['139'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('141',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('142',plain,
    ( ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
 != ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('146',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('147',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('151',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('157',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('160',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('163',plain,(
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
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['157','171'])).

thf('173',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('177',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('179',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['154','182'])).

thf('184',plain,(
    m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('186',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ X25 @ X23 )
      | ~ ( m1_orders_2 @ X25 @ X24 @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['187','188','189','190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['184','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['183','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['198','201'])).

thf('203',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('204',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['149','207'])).

thf('209',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('210',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('211',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','212'])).

thf('214',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['217','218','219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['214','222'])).

thf('224',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['213','223'])).

thf('225',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','212'])).

thf('226',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('227',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('228',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('229',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['226','231'])).

thf('233',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','212'])).

thf('234',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('235',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('237',plain,(
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
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['237','238','239','240','241'])).

thf('243',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['234','242'])).

thf('244',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['233','245'])).

thf('247',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','212'])).

thf('251',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('253',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('255',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('257',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['251','257'])).

thf('259',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['258','259','260','261','262'])).

thf('264',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['250','263'])).

thf('265',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['249','264'])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['232','266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('272',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('274',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_orders_2 @ X20 @ X21 @ X22 ) )
      | ( r2_orders_2 @ X20 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['272','275'])).

thf('277',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['276','277','278','279','280','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['225','284'])).

thf('286',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('287',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['224','287'])).

thf('289',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','288'])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('294',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('296',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['294','297'])).

thf('299',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('300',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['298','299'])).

thf('301',plain,(
    $false ),
    inference(demod,[status(thm)],['144','300'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KeqLafdl1A
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 50.35/50.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 50.35/50.58  % Solved by: fo/fo7.sh
% 50.35/50.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 50.35/50.58  % done 12287 iterations in 50.146s
% 50.35/50.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 50.35/50.58  % SZS output start Refutation
% 50.35/50.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 50.35/50.58  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 50.35/50.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 50.35/50.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 50.35/50.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 50.35/50.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 50.35/50.58  thf(sk_B_type, type, sk_B: $i).
% 50.35/50.58  thf(sk_A_type, type, sk_A: $i).
% 50.35/50.58  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 50.35/50.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 50.35/50.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 50.35/50.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 50.35/50.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 50.35/50.58  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 50.35/50.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 50.35/50.58  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 50.35/50.58  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 50.35/50.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 50.35/50.58  thf(t71_orders_2, conjecture,
% 50.35/50.58    (![A:$i]:
% 50.35/50.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 50.35/50.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 50.35/50.58       ( ![B:$i]:
% 50.35/50.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 50.35/50.58           ( ![C:$i]:
% 50.35/50.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58               ( ![D:$i]:
% 50.35/50.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58                   ( ( ( r2_hidden @ B @ C ) & ( m1_orders_2 @ C @ A @ D ) ) =>
% 50.35/50.58                     ( ( k3_orders_2 @ A @ C @ B ) =
% 50.35/50.58                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 50.35/50.58  thf(zf_stmt_0, negated_conjecture,
% 50.35/50.58    (~( ![A:$i]:
% 50.35/50.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 50.35/50.58            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 50.35/50.58          ( ![B:$i]:
% 50.35/50.58            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 50.35/50.58              ( ![C:$i]:
% 50.35/50.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58                  ( ![D:$i]:
% 50.35/50.58                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58                      ( ( ( r2_hidden @ B @ C ) & ( m1_orders_2 @ C @ A @ D ) ) =>
% 50.35/50.58                        ( ( k3_orders_2 @ A @ C @ B ) =
% 50.35/50.58                          ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 50.35/50.58    inference('cnf.neg', [status(esa)], [t71_orders_2])).
% 50.35/50.58  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('1', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf(dt_k3_orders_2, axiom,
% 50.35/50.58    (![A:$i,B:$i,C:$i]:
% 50.35/50.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 50.35/50.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 50.35/50.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 50.35/50.58         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58       ( m1_subset_1 @
% 50.35/50.58         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 50.35/50.58  thf('2', plain,
% 50.35/50.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 50.35/50.58          | ~ (l1_orders_2 @ X14)
% 50.35/50.58          | ~ (v5_orders_2 @ X14)
% 50.35/50.58          | ~ (v4_orders_2 @ X14)
% 50.35/50.58          | ~ (v3_orders_2 @ X14)
% 50.35/50.58          | (v2_struct_0 @ X14)
% 50.35/50.58          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 50.35/50.58          | (m1_subset_1 @ (k3_orders_2 @ X14 @ X13 @ X15) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 50.35/50.58      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 50.35/50.58  thf('3', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 50.35/50.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['1', '2'])).
% 50.35/50.58  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('8', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 50.35/50.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 50.35/50.58  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('10', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.58      inference('clc', [status(thm)], ['8', '9'])).
% 50.35/50.58  thf('11', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('13', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('14', plain,
% 50.35/50.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 50.35/50.58          | ~ (l1_orders_2 @ X14)
% 50.35/50.58          | ~ (v5_orders_2 @ X14)
% 50.35/50.58          | ~ (v4_orders_2 @ X14)
% 50.35/50.58          | ~ (v3_orders_2 @ X14)
% 50.35/50.58          | (v2_struct_0 @ X14)
% 50.35/50.58          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 50.35/50.58          | (m1_subset_1 @ (k3_orders_2 @ X14 @ X13 @ X15) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 50.35/50.58      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 50.35/50.58  thf('15', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 50.35/50.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['13', '14'])).
% 50.35/50.58  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('17', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('20', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 50.35/50.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 50.35/50.58  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('22', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.58      inference('clc', [status(thm)], ['20', '21'])).
% 50.35/50.58  thf('23', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf(t7_subset_1, axiom,
% 50.35/50.58    (![A:$i,B:$i]:
% 50.35/50.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 50.35/50.58       ( ![C:$i]:
% 50.35/50.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 50.35/50.58           ( ( ![D:$i]:
% 50.35/50.58               ( ( m1_subset_1 @ D @ A ) =>
% 50.35/50.58                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 50.35/50.58             ( r1_tarski @ B @ C ) ) ) ) ))).
% 50.35/50.58  thf('24', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('25', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0 @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             X0)
% 50.35/50.58          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['23', '24'])).
% 50.35/50.58  thf('26', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['11', '25'])).
% 50.35/50.58  thf('27', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('28', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('29', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('30', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r1_tarski @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['28', '29'])).
% 50.35/50.58  thf('31', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['27', '30'])).
% 50.35/50.58  thf('32', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('33', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('34', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('35', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['33', '34'])).
% 50.35/50.58  thf('36', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['32', '35'])).
% 50.35/50.58  thf('37', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf(t57_orders_2, axiom,
% 50.35/50.58    (![A:$i]:
% 50.35/50.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 50.35/50.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 50.35/50.58       ( ![B:$i]:
% 50.35/50.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 50.35/50.58           ( ![C:$i]:
% 50.35/50.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 50.35/50.58               ( ![D:$i]:
% 50.35/50.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 50.35/50.58                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 50.35/50.58  thf('38', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | (r2_orders_2 @ X20 @ X19 @ X22)
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('39', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['37', '38'])).
% 50.35/50.58  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('44', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 50.35/50.58  thf('45', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['36', '44'])).
% 50.35/50.58  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('47', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['45', '46'])).
% 50.35/50.58  thf('48', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['31', '47'])).
% 50.35/50.58  thf('49', plain,
% 50.35/50.58      (((r2_orders_2 @ sk_A @ 
% 50.35/50.58         (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58          (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58         sk_B)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('simplify', [status(thm)], ['48'])).
% 50.35/50.58  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('51', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B))),
% 50.35/50.58      inference('clc', [status(thm)], ['49', '50'])).
% 50.35/50.58  thf('52', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['27', '30'])).
% 50.35/50.58  thf('53', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['32', '35'])).
% 50.35/50.58  thf('54', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('55', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | (r2_hidden @ X19 @ X21)
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('56', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['54', '55'])).
% 50.35/50.58  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('61', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 50.35/50.58  thf('62', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_D_1)
% 50.35/50.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['53', '61'])).
% 50.35/50.58  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('64', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_D_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['62', '63'])).
% 50.35/50.58  thf('65', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_D_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['52', '64'])).
% 50.35/50.58  thf('66', plain,
% 50.35/50.58      (((r2_hidden @ 
% 50.35/50.58         (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58          (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58         sk_D_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('simplify', [status(thm)], ['65'])).
% 50.35/50.58  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('68', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_D_1))),
% 50.35/50.58      inference('clc', [status(thm)], ['66', '67'])).
% 50.35/50.58  thf('69', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['27', '30'])).
% 50.35/50.58  thf('70', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('71', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf(t70_orders_2, axiom,
% 50.35/50.58    (![A:$i]:
% 50.35/50.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 50.35/50.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 50.35/50.58       ( ![B:$i]:
% 50.35/50.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 50.35/50.58           ( ![C:$i]:
% 50.35/50.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 50.35/50.58               ( ![D:$i]:
% 50.35/50.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58                   ( ![E:$i]:
% 50.35/50.58                     ( ( m1_subset_1 @
% 50.35/50.58                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 50.35/50.58                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 50.35/50.58                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 50.35/50.58                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 50.35/50.58  thf('72', plain,
% 50.35/50.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 50.35/50.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 50.35/50.58          | ~ (r2_orders_2 @ X27 @ X26 @ X29)
% 50.35/50.58          | ~ (r2_hidden @ X26 @ X28)
% 50.35/50.58          | ~ (r2_hidden @ X29 @ X30)
% 50.35/50.58          | ~ (m1_orders_2 @ X30 @ X27 @ X28)
% 50.35/50.58          | (r2_hidden @ X26 @ X30)
% 50.35/50.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 50.35/50.58          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 50.35/50.58          | ~ (l1_orders_2 @ X27)
% 50.35/50.58          | ~ (v5_orders_2 @ X27)
% 50.35/50.58          | ~ (v4_orders_2 @ X27)
% 50.35/50.58          | ~ (v3_orders_2 @ X27)
% 50.35/50.58          | (v2_struct_0 @ X27))),
% 50.35/50.58      inference('cnf', [status(esa)], [t70_orders_2])).
% 50.35/50.58  thf('73', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ X2 @ X1)
% 50.35/50.58          | ~ (m1_orders_2 @ X1 @ sk_A @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | ~ (r2_hidden @ X2 @ sk_D_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X2 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['71', '72'])).
% 50.35/50.58  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('75', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('78', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ X2 @ X1)
% 50.35/50.58          | ~ (m1_orders_2 @ X1 @ sk_A @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | ~ (r2_hidden @ X2 @ sk_D_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X2 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 50.35/50.58  thf('79', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ sk_C_1)
% 50.35/50.58          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)
% 50.35/50.58          | (r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['70', '78'])).
% 50.35/50.58  thf('80', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('81', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ sk_C_1)
% 50.35/50.58          | (r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['79', '80'])).
% 50.35/50.58  thf('82', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58          | (v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ 
% 50.35/50.58               (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58                (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58               sk_D_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ 
% 50.35/50.58               (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58                (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58               X0))),
% 50.35/50.58      inference('sup-', [status(thm)], ['69', '81'])).
% 50.35/50.58  thf('83', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ 
% 50.35/50.58               (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58                (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58               X0)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | (r2_hidden @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_C_1)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (v2_struct_0 @ sk_A)
% 50.35/50.58          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['68', '82'])).
% 50.35/50.58  thf('84', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ 
% 50.35/50.58               (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58                (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58               X0)
% 50.35/50.58          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('simplify', [status(thm)], ['83'])).
% 50.35/50.58  thf('85', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (r2_hidden @ sk_B @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['51', '84'])).
% 50.35/50.58  thf('86', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('88', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['85', '86', '87'])).
% 50.35/50.58  thf('89', plain,
% 50.35/50.58      (((v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('simplify', [status(thm)], ['88'])).
% 50.35/50.58  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('91', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1))),
% 50.35/50.58      inference('clc', [status(thm)], ['89', '90'])).
% 50.35/50.58  thf('92', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('93', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('94', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_C_1)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['92', '93'])).
% 50.35/50.58  thf('95', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.58      inference('sup-', [status(thm)], ['91', '94'])).
% 50.35/50.58  thf('96', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('97', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('demod', [status(thm)], ['95', '96'])).
% 50.35/50.58  thf('98', plain,
% 50.35/50.58      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ sk_C_1)),
% 50.35/50.58      inference('simplify', [status(thm)], ['97'])).
% 50.35/50.58  thf(d3_tarski, axiom,
% 50.35/50.58    (![A:$i,B:$i]:
% 50.35/50.58     ( ( r1_tarski @ A @ B ) <=>
% 50.35/50.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 50.35/50.58  thf('99', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         (~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | (r2_hidden @ X0 @ X2)
% 50.35/50.58          | ~ (r1_tarski @ X1 @ X2))),
% 50.35/50.58      inference('cnf', [status(esa)], [d3_tarski])).
% 50.35/50.58  thf('100', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['98', '99'])).
% 50.35/50.58  thf('101', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['26', '100'])).
% 50.35/50.58  thf('102', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('103', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('104', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('105', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0 @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['103', '104'])).
% 50.35/50.58  thf('106', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['102', '105'])).
% 50.35/50.58  thf('107', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['11', '25'])).
% 50.35/50.58  thf('108', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 50.35/50.58  thf('109', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['107', '108'])).
% 50.35/50.58  thf('110', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('111', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['109', '110'])).
% 50.35/50.58  thf('112', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['106', '111'])).
% 50.35/50.58  thf('113', plain,
% 50.35/50.58      (((r2_orders_2 @ sk_A @ 
% 50.35/50.58         (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58         sk_B)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('simplify', [status(thm)], ['112'])).
% 50.35/50.58  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('115', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B))),
% 50.35/50.58      inference('clc', [status(thm)], ['113', '114'])).
% 50.35/50.58  thf('116', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['102', '105'])).
% 50.35/50.58  thf('117', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('118', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('119', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_orders_2 @ X20 @ X19 @ X22)
% 50.35/50.58          | ~ (r2_hidden @ X19 @ X21)
% 50.35/50.58          | (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('120', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 50.35/50.58          | ~ (r2_hidden @ X1 @ sk_C_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['118', '119'])).
% 50.35/50.58  thf('121', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('122', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('123', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('125', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 50.35/50.58          | ~ (r2_hidden @ X1 @ sk_C_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 50.35/50.58  thf('126', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['117', '125'])).
% 50.35/50.58  thf('127', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | ~ (r2_hidden @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_C_1)
% 50.35/50.58        | ~ (r2_orders_2 @ sk_A @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_B))),
% 50.35/50.58      inference('sup-', [status(thm)], ['116', '126'])).
% 50.35/50.58  thf('128', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | ~ (r2_hidden @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['115', '127'])).
% 50.35/50.58  thf('129', plain,
% 50.35/50.58      (((v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | ~ (r2_hidden @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('simplify', [status(thm)], ['128'])).
% 50.35/50.58  thf('130', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['101', '129'])).
% 50.35/50.58  thf('131', plain,
% 50.35/50.58      (((v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('simplify', [status(thm)], ['130'])).
% 50.35/50.58  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('133', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('clc', [status(thm)], ['131', '132'])).
% 50.35/50.58  thf('134', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('135', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('136', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (r2_hidden @ 
% 50.35/50.58               (sk_D @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0 @ 
% 50.35/50.58                (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58               (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['134', '135'])).
% 50.35/50.58  thf('137', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.58      inference('sup-', [status(thm)], ['133', '136'])).
% 50.35/50.58  thf('138', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('139', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('demod', [status(thm)], ['137', '138'])).
% 50.35/50.58  thf('140', plain,
% 50.35/50.58      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 50.35/50.58      inference('simplify', [status(thm)], ['139'])).
% 50.35/50.58  thf(d10_xboole_0, axiom,
% 50.35/50.58    (![A:$i,B:$i]:
% 50.35/50.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 50.35/50.58  thf('141', plain,
% 50.35/50.58      (![X4 : $i, X6 : $i]:
% 50.35/50.58         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 50.35/50.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 50.35/50.58  thf('142', plain,
% 50.35/50.58      ((~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | ((k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 50.35/50.58            = (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['140', '141'])).
% 50.35/50.58  thf('143', plain,
% 50.35/50.58      (((k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 50.35/50.58         != (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('144', plain,
% 50.35/50.58      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.58      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 50.35/50.58  thf('145', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('146', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('147', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('148', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             X0)
% 50.35/50.58          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['146', '147'])).
% 50.35/50.58  thf('149', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['145', '148'])).
% 50.35/50.58  thf('150', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('151', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('152', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('153', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_D_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['151', '152'])).
% 50.35/50.58  thf('154', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_D_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['150', '153'])).
% 50.35/50.58  thf('155', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('156', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r1_tarski @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['28', '29'])).
% 50.35/50.58  thf('157', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['155', '156'])).
% 50.35/50.58  thf('158', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('159', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['33', '34'])).
% 50.35/50.58  thf('160', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['158', '159'])).
% 50.35/50.58  thf('161', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('162', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | (r2_hidden @ X19 @ X21)
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('163', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['161', '162'])).
% 50.35/50.58  thf('164', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('165', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('166', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('167', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('168', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 50.35/50.58  thf('169', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['160', '168'])).
% 50.35/50.58  thf('170', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('171', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['169', '170'])).
% 50.35/50.58  thf('172', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['157', '171'])).
% 50.35/50.58  thf('173', plain,
% 50.35/50.58      (((r2_hidden @ 
% 50.35/50.58         (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58          (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58         sk_C_1)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('simplify', [status(thm)], ['172'])).
% 50.35/50.58  thf('174', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('175', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1))),
% 50.35/50.58      inference('clc', [status(thm)], ['173', '174'])).
% 50.35/50.58  thf('176', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_C_1)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['92', '93'])).
% 50.35/50.58  thf('177', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.58      inference('sup-', [status(thm)], ['175', '176'])).
% 50.35/50.58  thf('178', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('179', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 50.35/50.58      inference('demod', [status(thm)], ['177', '178'])).
% 50.35/50.58  thf('180', plain,
% 50.35/50.58      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)),
% 50.35/50.58      inference('simplify', [status(thm)], ['179'])).
% 50.35/50.58  thf('181', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         (~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | (r2_hidden @ X0 @ X2)
% 50.35/50.58          | ~ (r1_tarski @ X1 @ X2))),
% 50.35/50.58      inference('cnf', [status(esa)], [d3_tarski])).
% 50.35/50.58  thf('182', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r2_hidden @ X0 @ sk_C_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['180', '181'])).
% 50.35/50.58  thf('183', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_D_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['154', '182'])).
% 50.35/50.58  thf('184', plain, ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('185', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf(t67_orders_2, axiom,
% 50.35/50.58    (![A:$i]:
% 50.35/50.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 50.35/50.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 50.35/50.58       ( ![B:$i]:
% 50.35/50.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 50.35/50.58           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 50.35/50.58  thf('186', plain,
% 50.35/50.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 50.35/50.58          | (r1_tarski @ X25 @ X23)
% 50.35/50.58          | ~ (m1_orders_2 @ X25 @ X24 @ X23)
% 50.35/50.58          | ~ (l1_orders_2 @ X24)
% 50.35/50.58          | ~ (v5_orders_2 @ X24)
% 50.35/50.58          | ~ (v4_orders_2 @ X24)
% 50.35/50.58          | ~ (v3_orders_2 @ X24)
% 50.35/50.58          | (v2_struct_0 @ X24))),
% 50.35/50.58      inference('cnf', [status(esa)], [t67_orders_2])).
% 50.35/50.58  thf('187', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_D_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['185', '186'])).
% 50.35/50.58  thf('188', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('189', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('190', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('191', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('192', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_D_1))),
% 50.35/50.58      inference('demod', [status(thm)], ['187', '188', '189', '190', '191'])).
% 50.35/50.58  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('194', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r1_tarski @ X0 @ sk_D_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1))),
% 50.35/50.58      inference('clc', [status(thm)], ['192', '193'])).
% 50.35/50.58  thf('195', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 50.35/50.58      inference('sup-', [status(thm)], ['184', '194'])).
% 50.35/50.58  thf('196', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         (~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | (r2_hidden @ X0 @ X2)
% 50.35/50.58          | ~ (r1_tarski @ X1 @ X2))),
% 50.35/50.58      inference('cnf', [status(esa)], [d3_tarski])).
% 50.35/50.58  thf('197', plain,
% 50.35/50.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['195', '196'])).
% 50.35/50.58  thf('198', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ sk_D_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58            (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_D_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['183', '197'])).
% 50.35/50.58  thf('199', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('200', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('201', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_D_1)
% 50.35/50.58          | (r1_tarski @ X0 @ sk_D_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['199', '200'])).
% 50.35/50.58  thf('202', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 50.35/50.58        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.58      inference('sup-', [status(thm)], ['198', '201'])).
% 50.35/50.58  thf('203', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('204', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1))),
% 50.35/50.58      inference('demod', [status(thm)], ['202', '203'])).
% 50.35/50.58  thf('205', plain,
% 50.35/50.58      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)),
% 50.35/50.58      inference('simplify', [status(thm)], ['204'])).
% 50.35/50.58  thf('206', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         (~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | (r2_hidden @ X0 @ X2)
% 50.35/50.58          | ~ (r1_tarski @ X1 @ X2))),
% 50.35/50.58      inference('cnf', [status(esa)], [d3_tarski])).
% 50.35/50.58  thf('207', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r2_hidden @ X0 @ sk_D_1)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['205', '206'])).
% 50.35/50.58  thf('208', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_D_1))),
% 50.35/50.58      inference('sup-', [status(thm)], ['149', '207'])).
% 50.35/50.58  thf('209', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf('210', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.58  thf('211', plain,
% 50.35/50.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.58          | (r1_tarski @ X9 @ X7)
% 50.35/50.58          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 50.35/50.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.58  thf('212', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.58          | (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 50.35/50.58              (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['210', '211'])).
% 50.35/50.58  thf('213', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['209', '212'])).
% 50.35/50.58  thf('214', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('215', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('216', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_orders_2 @ X20 @ X19 @ X22)
% 50.35/50.58          | ~ (r2_hidden @ X19 @ X21)
% 50.35/50.58          | (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('217', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (r2_hidden @ X1 @ sk_D_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['215', '216'])).
% 50.35/50.58  thf('218', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('219', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('220', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('221', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('222', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 50.35/50.58          | ~ (r2_hidden @ X1 @ sk_D_1)
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['217', '218', '219', '220', '221'])).
% 50.35/50.58  thf('223', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ sk_D_1)
% 50.35/50.58          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['214', '222'])).
% 50.35/50.58  thf('224', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | ~ (r2_hidden @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_D_1)
% 50.35/50.58        | ~ (r2_orders_2 @ sk_A @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             sk_B))),
% 50.35/50.58      inference('sup-', [status(thm)], ['213', '223'])).
% 50.35/50.58  thf('225', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['209', '212'])).
% 50.35/50.58  thf('226', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['145', '148'])).
% 50.35/50.58  thf('227', plain,
% 50.35/50.58      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.58  thf(t3_subset, axiom,
% 50.35/50.58    (![A:$i,B:$i]:
% 50.35/50.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 50.35/50.58  thf('228', plain,
% 50.35/50.58      (![X10 : $i, X11 : $i]:
% 50.35/50.58         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 50.35/50.58      inference('cnf', [status(esa)], [t3_subset])).
% 50.35/50.58  thf('229', plain,
% 50.35/50.58      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['227', '228'])).
% 50.35/50.58  thf('230', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         (~ (r2_hidden @ X0 @ X1)
% 50.35/50.58          | (r2_hidden @ X0 @ X2)
% 50.35/50.58          | ~ (r1_tarski @ X1 @ X2))),
% 50.35/50.58      inference('cnf', [status(esa)], [d3_tarski])).
% 50.35/50.58  thf('231', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['229', '230'])).
% 50.35/50.58  thf('232', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['226', '231'])).
% 50.35/50.58  thf('233', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['209', '212'])).
% 50.35/50.58  thf('234', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (r2_hidden @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['145', '148'])).
% 50.35/50.58  thf('235', plain,
% 50.35/50.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('236', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | (r2_orders_2 @ X20 @ X19 @ X22)
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('237', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['235', '236'])).
% 50.35/50.58  thf('238', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('239', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('240', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('241', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('242', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i]:
% 50.35/50.58         ((v2_struct_0 @ sk_A)
% 50.35/50.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 50.35/50.58          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('demod', [status(thm)], ['237', '238', '239', '240', '241'])).
% 50.35/50.58  thf('243', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['234', '242'])).
% 50.35/50.58  thf('244', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('245', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | ~ (m1_subset_1 @ 
% 50.35/50.58             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58             (u1_struct_0 @ sk_A))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('demod', [status(thm)], ['243', '244'])).
% 50.35/50.58  thf('246', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['233', '245'])).
% 50.35/50.58  thf('247', plain,
% 50.35/50.58      (((r2_orders_2 @ sk_A @ 
% 50.35/50.58         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58          (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58         sk_B)
% 50.35/50.58        | (v2_struct_0 @ sk_A)
% 50.35/50.58        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.58      inference('simplify', [status(thm)], ['246'])).
% 50.35/50.58  thf('248', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('249', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (r2_orders_2 @ sk_A @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           sk_B))),
% 50.35/50.58      inference('clc', [status(thm)], ['247', '248'])).
% 50.35/50.58  thf('250', plain,
% 50.35/50.58      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.58         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.58        | (m1_subset_1 @ 
% 50.35/50.58           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.58            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.58           (u1_struct_0 @ sk_A)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['209', '212'])).
% 50.35/50.58  thf('251', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('252', plain,
% 50.35/50.58      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 50.35/50.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 50.35/50.58  thf('253', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 50.35/50.58      inference('simplify', [status(thm)], ['252'])).
% 50.35/50.58  thf('254', plain,
% 50.35/50.58      (![X10 : $i, X12 : $i]:
% 50.35/50.58         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 50.35/50.58      inference('cnf', [status(esa)], [t3_subset])).
% 50.35/50.58  thf('255', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 50.35/50.58      inference('sup-', [status(thm)], ['253', '254'])).
% 50.35/50.58  thf('256', plain,
% 50.35/50.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.58          | ~ (r2_orders_2 @ X20 @ X19 @ X22)
% 50.35/50.58          | ~ (r2_hidden @ X19 @ X21)
% 50.35/50.58          | (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.58          | ~ (l1_orders_2 @ X20)
% 50.35/50.58          | ~ (v5_orders_2 @ X20)
% 50.35/50.58          | ~ (v4_orders_2 @ X20)
% 50.35/50.58          | ~ (v3_orders_2 @ X20)
% 50.35/50.58          | (v2_struct_0 @ X20))),
% 50.35/50.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.58  thf('257', plain,
% 50.35/50.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.58         ((v2_struct_0 @ X0)
% 50.35/50.58          | ~ (v3_orders_2 @ X0)
% 50.35/50.58          | ~ (v4_orders_2 @ X0)
% 50.35/50.58          | ~ (v5_orders_2 @ X0)
% 50.35/50.58          | ~ (l1_orders_2 @ X0)
% 50.35/50.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 50.35/50.58          | (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ (u1_struct_0 @ X0) @ X1))
% 50.35/50.58          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 50.35/50.58          | ~ (r2_orders_2 @ X0 @ X2 @ X1)
% 50.35/50.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 50.35/50.58      inference('sup-', [status(thm)], ['255', '256'])).
% 50.35/50.58  thf('258', plain,
% 50.35/50.58      (![X0 : $i]:
% 50.35/50.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 50.35/50.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.58          | (r2_hidden @ X0 @ 
% 50.35/50.58             (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.58          | ~ (l1_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v5_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v4_orders_2 @ sk_A)
% 50.35/50.58          | ~ (v3_orders_2 @ sk_A)
% 50.35/50.58          | (v2_struct_0 @ sk_A))),
% 50.35/50.58      inference('sup-', [status(thm)], ['251', '257'])).
% 50.35/50.58  thf('259', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('260', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.58  thf('261', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('262', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('263', plain,
% 50.35/50.59      (![X0 : $i]:
% 50.35/50.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.59          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 50.35/50.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 50.35/50.59          | (r2_hidden @ X0 @ 
% 50.35/50.59             (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.59          | (v2_struct_0 @ sk_A))),
% 50.35/50.59      inference('demod', [status(thm)], ['258', '259', '260', '261', '262'])).
% 50.35/50.59  thf('264', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (v2_struct_0 @ sk_A)
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.59        | ~ (r2_hidden @ 
% 50.35/50.59             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59             (u1_struct_0 @ sk_A))
% 50.35/50.59        | ~ (r2_orders_2 @ sk_A @ 
% 50.35/50.59             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59             sk_B))),
% 50.35/50.59      inference('sup-', [status(thm)], ['250', '263'])).
% 50.35/50.59  thf('265', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | ~ (r2_hidden @ 
% 50.35/50.59             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59             (u1_struct_0 @ sk_A))
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.59        | (v2_struct_0 @ sk_A)
% 50.35/50.59        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('sup-', [status(thm)], ['249', '264'])).
% 50.35/50.59  thf('266', plain,
% 50.35/50.59      (((v2_struct_0 @ sk_A)
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.59        | ~ (r2_hidden @ 
% 50.35/50.59             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59             (u1_struct_0 @ sk_A))
% 50.35/50.59        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('simplify', [status(thm)], ['265'])).
% 50.35/50.59  thf('267', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.59        | (v2_struct_0 @ sk_A))),
% 50.35/50.59      inference('sup-', [status(thm)], ['232', '266'])).
% 50.35/50.59  thf('268', plain,
% 50.35/50.59      (((v2_struct_0 @ sk_A)
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 50.35/50.59        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('simplify', [status(thm)], ['267'])).
% 50.35/50.59  thf('269', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('270', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 50.35/50.59      inference('clc', [status(thm)], ['268', '269'])).
% 50.35/50.59  thf('271', plain,
% 50.35/50.59      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.59      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 50.35/50.59  thf('272', plain,
% 50.35/50.59      ((r2_hidden @ 
% 50.35/50.59        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59        (k3_orders_2 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))),
% 50.35/50.59      inference('clc', [status(thm)], ['270', '271'])).
% 50.35/50.59  thf('273', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 50.35/50.59      inference('sup-', [status(thm)], ['253', '254'])).
% 50.35/50.59  thf('274', plain,
% 50.35/50.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 50.35/50.59         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 50.35/50.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 50.35/50.59          | ~ (r2_hidden @ X19 @ (k3_orders_2 @ X20 @ X21 @ X22))
% 50.35/50.59          | (r2_orders_2 @ X20 @ X19 @ X22)
% 50.35/50.59          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 50.35/50.59          | ~ (l1_orders_2 @ X20)
% 50.35/50.59          | ~ (v5_orders_2 @ X20)
% 50.35/50.59          | ~ (v4_orders_2 @ X20)
% 50.35/50.59          | ~ (v3_orders_2 @ X20)
% 50.35/50.59          | (v2_struct_0 @ X20))),
% 50.35/50.59      inference('cnf', [status(esa)], [t57_orders_2])).
% 50.35/50.59  thf('275', plain,
% 50.35/50.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.35/50.59         ((v2_struct_0 @ X0)
% 50.35/50.59          | ~ (v3_orders_2 @ X0)
% 50.35/50.59          | ~ (v4_orders_2 @ X0)
% 50.35/50.59          | ~ (v5_orders_2 @ X0)
% 50.35/50.59          | ~ (l1_orders_2 @ X0)
% 50.35/50.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 50.35/50.59          | (r2_orders_2 @ X0 @ X2 @ X1)
% 50.35/50.59          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ (u1_struct_0 @ X0) @ X1))
% 50.35/50.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 50.35/50.59      inference('sup-', [status(thm)], ['273', '274'])).
% 50.35/50.59  thf('276', plain,
% 50.35/50.59      ((~ (m1_subset_1 @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (u1_struct_0 @ sk_A))
% 50.35/50.59        | (r2_orders_2 @ sk_A @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           sk_B)
% 50.35/50.59        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 50.35/50.59        | ~ (l1_orders_2 @ sk_A)
% 50.35/50.59        | ~ (v5_orders_2 @ sk_A)
% 50.35/50.59        | ~ (v4_orders_2 @ sk_A)
% 50.35/50.59        | ~ (v3_orders_2 @ sk_A)
% 50.35/50.59        | (v2_struct_0 @ sk_A))),
% 50.35/50.59      inference('sup-', [status(thm)], ['272', '275'])).
% 50.35/50.59  thf('277', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('278', plain, ((l1_orders_2 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('279', plain, ((v5_orders_2 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('280', plain, ((v4_orders_2 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('281', plain, ((v3_orders_2 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('282', plain,
% 50.35/50.59      ((~ (m1_subset_1 @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (u1_struct_0 @ sk_A))
% 50.35/50.59        | (r2_orders_2 @ sk_A @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           sk_B)
% 50.35/50.59        | (v2_struct_0 @ sk_A))),
% 50.35/50.59      inference('demod', [status(thm)],
% 50.35/50.59                ['276', '277', '278', '279', '280', '281'])).
% 50.35/50.59  thf('283', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('284', plain,
% 50.35/50.59      (((r2_orders_2 @ sk_A @ 
% 50.35/50.59         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59          (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59         sk_B)
% 50.35/50.59        | ~ (m1_subset_1 @ 
% 50.35/50.59             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59             (u1_struct_0 @ sk_A)))),
% 50.35/50.59      inference('clc', [status(thm)], ['282', '283'])).
% 50.35/50.59  thf('285', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r2_orders_2 @ sk_A @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           sk_B))),
% 50.35/50.59      inference('sup-', [status(thm)], ['225', '284'])).
% 50.35/50.59  thf('286', plain,
% 50.35/50.59      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.59      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 50.35/50.59  thf('287', plain,
% 50.35/50.59      ((r2_orders_2 @ sk_A @ 
% 50.35/50.59        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59        sk_B)),
% 50.35/50.59      inference('clc', [status(thm)], ['285', '286'])).
% 50.35/50.59  thf('288', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (v2_struct_0 @ sk_A)
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | ~ (r2_hidden @ 
% 50.35/50.59             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59             sk_D_1))),
% 50.35/50.59      inference('demod', [status(thm)], ['224', '287'])).
% 50.35/50.59  thf('289', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (v2_struct_0 @ sk_A)
% 50.35/50.59        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('sup-', [status(thm)], ['208', '288'])).
% 50.35/50.59  thf('290', plain,
% 50.35/50.59      (((v2_struct_0 @ sk_A)
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('simplify', [status(thm)], ['289'])).
% 50.35/50.59  thf('291', plain, (~ (v2_struct_0 @ sk_A)),
% 50.35/50.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.35/50.59  thf('292', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | (r2_hidden @ 
% 50.35/50.59           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('clc', [status(thm)], ['290', '291'])).
% 50.35/50.59  thf('293', plain,
% 50.35/50.59      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.59      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 50.35/50.59  thf('294', plain,
% 50.35/50.59      ((r2_hidden @ 
% 50.35/50.59        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.59      inference('clc', [status(thm)], ['292', '293'])).
% 50.35/50.59  thf('295', plain,
% 50.35/50.59      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 50.35/50.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.59      inference('sup-', [status(thm)], ['0', '10'])).
% 50.35/50.59  thf('296', plain,
% 50.35/50.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 50.35/50.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 50.35/50.59          | (r1_tarski @ X9 @ X7)
% 50.35/50.59          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 50.35/50.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 50.35/50.59      inference('cnf', [status(esa)], [t7_subset_1])).
% 50.35/50.59  thf('297', plain,
% 50.35/50.59      (![X0 : $i]:
% 50.35/50.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 50.35/50.59          | ~ (r2_hidden @ 
% 50.35/50.59               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 50.35/50.59                (u1_struct_0 @ sk_A)) @ 
% 50.35/50.59               (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 50.35/50.59      inference('sup-', [status(thm)], ['295', '296'])).
% 50.35/50.59  thf('298', plain,
% 50.35/50.59      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 50.35/50.59        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 50.35/50.59      inference('sup-', [status(thm)], ['294', '297'])).
% 50.35/50.59  thf('299', plain,
% 50.35/50.59      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 50.35/50.59      inference('sup-', [status(thm)], ['12', '22'])).
% 50.35/50.59  thf('300', plain,
% 50.35/50.59      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 50.35/50.59        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 50.35/50.59      inference('demod', [status(thm)], ['298', '299'])).
% 50.35/50.59  thf('301', plain, ($false), inference('demod', [status(thm)], ['144', '300'])).
% 50.35/50.59  
% 50.35/50.59  % SZS output end Refutation
% 50.35/50.59  
% 50.35/50.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
