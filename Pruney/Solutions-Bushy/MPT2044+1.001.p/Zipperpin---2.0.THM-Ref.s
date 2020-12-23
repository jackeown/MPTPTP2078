%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2lflgmGGm

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 259 expanded)
%              Number of leaves         :   16 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  546 (3305 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(a_2_0_yellow19_type,type,(
    a_2_0_yellow19: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t3_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) )
            <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) )
              <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_yellow19])).

thf('0',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_0_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_yellow19 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( A = D )
            & ( m1_connsp_2 @ D @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r2_hidden @ X4 @ ( a_2_0_yellow19 @ X2 @ X3 ) )
      | ~ ( m1_connsp_2 @ X5 @ X2 @ X3 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow19])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ~ ( m1_connsp_2 @ X5 @ X2 @ X3 )
      | ( r2_hidden @ X5 @ ( a_2_0_yellow19 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k1_yellow19 @ A @ B )
            = ( a_2_0_yellow19 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_yellow19 @ X1 @ X0 )
        = ( a_2_0_yellow19 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_yellow19])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_yellow19 @ sk_A @ sk_B )
      = ( a_2_0_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow19 @ sk_A @ sk_B )
      = ( a_2_0_yellow19 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_yellow19 @ sk_A @ sk_B )
    = ( a_2_0_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','24'])).

thf('26',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,
    ( ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','24','28'])).

thf('30',plain,(
    r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( m1_connsp_2 @ ( sk_D @ X3 @ X2 @ X4 ) @ X2 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( a_2_0_yellow19 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow19])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow19 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_yellow19 @ sk_A @ sk_B )
    = ( a_2_0_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_connsp_2 @ ( sk_D @ sk_B @ sk_A @ sk_C ) @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X4
        = ( sk_D @ X3 @ X2 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ ( a_2_0_yellow19 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow19])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow19 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow19 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k1_yellow19 @ sk_A @ sk_B )
    = ( a_2_0_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    r2_hidden @ sk_C @ ( k1_yellow19 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','24','28'])).

thf('54',plain,
    ( sk_C
    = ( sk_D @ sk_B @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['40','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['26','55'])).


%------------------------------------------------------------------------------
