%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.arcU4uI7co

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:27 EST 2020

% Result     : Theorem 17.45s
% Output     : Refutation 17.45s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 748 expanded)
%              Number of leaves         :   30 ( 227 expanded)
%              Depth                    :   21
%              Number of atoms          : 1381 (12970 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t23_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                 => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                   => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_waybel_9])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( m1_connsp_2 @ X39 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_connsp_2 @ X30 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_connsp_2 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X6 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( m1_connsp_2 @ X39 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t39_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
              <=> ( ( r2_hidden @ B @ C )
                  & ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r2_hidden @ X34 @ X36 )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( r2_hidden @ X36 @ ( u1_struct_0 @ ( k9_yellow_6 @ X35 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( v3_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('66',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('68',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r2_hidden @ X36 @ ( u1_struct_0 @ ( k9_yellow_6 @ X35 @ X34 ) ) )
      | ( v3_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ( m1_subset_1 @ X16 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('88',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('93',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['91','96'])).

thf('98',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','103'])).

thf('105',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('107',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r2_hidden @ X36 @ ( u1_struct_0 @ ( k9_yellow_6 @ X35 @ X34 ) ) )
      | ( v3_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('121',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','121'])).

thf('123',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('124',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('125',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['122','125'])).

thf('127',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('129',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v3_pre_topc @ sk_D_1 @ sk_A ),
    inference(clc,[status(thm)],['126','129'])).

thf('131',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['105','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','131'])).

thf('133',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('138',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('139',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.arcU4uI7co
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:40:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 17.45/17.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.45/17.67  % Solved by: fo/fo7.sh
% 17.45/17.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.45/17.67  % done 5440 iterations in 17.221s
% 17.45/17.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.45/17.67  % SZS output start Refutation
% 17.45/17.67  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 17.45/17.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.45/17.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 17.45/17.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.45/17.67  thf(sk_B_type, type, sk_B: $i > $i).
% 17.45/17.67  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 17.45/17.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 17.45/17.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.45/17.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.45/17.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 17.45/17.67  thf(sk_C_type, type, sk_C: $i).
% 17.45/17.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.45/17.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.45/17.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.45/17.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 17.45/17.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 17.45/17.67  thf(sk_A_type, type, sk_A: $i).
% 17.45/17.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 17.45/17.67  thf(t23_waybel_9, conjecture,
% 17.45/17.67    (![A:$i]:
% 17.45/17.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.45/17.67       ( ![B:$i]:
% 17.45/17.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.45/17.67           ( ![C:$i]:
% 17.45/17.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.45/17.67               ( ![D:$i]:
% 17.45/17.67                 ( ( m1_subset_1 @
% 17.45/17.67                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.45/17.67                   ( m1_subset_1 @
% 17.45/17.67                     ( k2_xboole_0 @ C @ D ) @ 
% 17.45/17.67                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 17.45/17.67  thf(zf_stmt_0, negated_conjecture,
% 17.45/17.67    (~( ![A:$i]:
% 17.45/17.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 17.45/17.67            ( l1_pre_topc @ A ) ) =>
% 17.45/17.67          ( ![B:$i]:
% 17.45/17.67            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.45/17.67              ( ![C:$i]:
% 17.45/17.67                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.45/17.67                  ( ![D:$i]:
% 17.45/17.67                    ( ( m1_subset_1 @
% 17.45/17.67                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.45/17.67                      ( m1_subset_1 @
% 17.45/17.67                        ( k2_xboole_0 @ C @ D ) @ 
% 17.45/17.67                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 17.45/17.67    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 17.45/17.67  thf('0', plain,
% 17.45/17.67      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('2', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf(t21_waybel_9, axiom,
% 17.45/17.67    (![A:$i]:
% 17.45/17.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.45/17.67       ( ![B:$i]:
% 17.45/17.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.45/17.67           ( ![C:$i]:
% 17.45/17.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.45/17.67               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 17.45/17.67  thf('3', plain,
% 17.45/17.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 17.45/17.67          | (m1_connsp_2 @ X39 @ X38 @ X37)
% 17.45/17.67          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 17.45/17.67          | ~ (l1_pre_topc @ X38)
% 17.45/17.67          | ~ (v2_pre_topc @ X38)
% 17.45/17.67          | (v2_struct_0 @ X38))),
% 17.45/17.67      inference('cnf', [status(esa)], [t21_waybel_9])).
% 17.45/17.67  thf('4', plain,
% 17.45/17.67      (((v2_struct_0 @ sk_A)
% 17.45/17.67        | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67        | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['2', '3'])).
% 17.45/17.67  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('8', plain,
% 17.45/17.67      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 17.45/17.67      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 17.45/17.67  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('10', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 17.45/17.67      inference('clc', [status(thm)], ['8', '9'])).
% 17.45/17.67  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf(dt_m1_connsp_2, axiom,
% 17.45/17.67    (![A:$i,B:$i]:
% 17.45/17.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 17.45/17.67         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 17.45/17.67       ( ![C:$i]:
% 17.45/17.67         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 17.45/17.67           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 17.45/17.67  thf('12', plain,
% 17.45/17.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.45/17.67         (~ (l1_pre_topc @ X28)
% 17.45/17.67          | ~ (v2_pre_topc @ X28)
% 17.45/17.67          | (v2_struct_0 @ X28)
% 17.45/17.67          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 17.45/17.67          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 17.45/17.67          | ~ (m1_connsp_2 @ X30 @ X28 @ X29))),
% 17.45/17.67      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 17.45/17.67  thf('13', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 17.45/17.67          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | (v2_struct_0 @ sk_A)
% 17.45/17.67          | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67          | ~ (l1_pre_topc @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['11', '12'])).
% 17.45/17.67  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('16', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 17.45/17.67          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | (v2_struct_0 @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['13', '14', '15'])).
% 17.45/17.67  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('18', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 17.45/17.67      inference('clc', [status(thm)], ['16', '17'])).
% 17.45/17.67  thf('19', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['10', '18'])).
% 17.45/17.67  thf(t6_connsp_2, axiom,
% 17.45/17.67    (![A:$i]:
% 17.45/17.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.45/17.67       ( ![B:$i]:
% 17.45/17.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.45/17.67           ( ![C:$i]:
% 17.45/17.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 17.45/17.67               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 17.45/17.67  thf('20', plain,
% 17.45/17.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 17.45/17.67          | ~ (m1_connsp_2 @ X31 @ X32 @ X33)
% 17.45/17.67          | (r2_hidden @ X33 @ X31)
% 17.45/17.67          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 17.45/17.67          | ~ (l1_pre_topc @ X32)
% 17.45/17.67          | ~ (v2_pre_topc @ X32)
% 17.45/17.67          | (v2_struct_0 @ X32))),
% 17.45/17.67      inference('cnf', [status(esa)], [t6_connsp_2])).
% 17.45/17.67  thf('21', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v2_struct_0 @ sk_A)
% 17.45/17.67          | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67          | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 17.45/17.67          | (r2_hidden @ X0 @ sk_C)
% 17.45/17.67          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 17.45/17.67      inference('sup-', [status(thm)], ['19', '20'])).
% 17.45/17.67  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('24', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v2_struct_0 @ sk_A)
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 17.45/17.67          | (r2_hidden @ X0 @ sk_C)
% 17.45/17.67          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 17.45/17.67      inference('demod', [status(thm)], ['21', '22', '23'])).
% 17.45/17.67  thf('25', plain,
% 17.45/17.67      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 17.45/17.67        | (r2_hidden @ sk_B_1 @ sk_C)
% 17.45/17.67        | (v2_struct_0 @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['1', '24'])).
% 17.45/17.67  thf('26', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 17.45/17.67      inference('clc', [status(thm)], ['8', '9'])).
% 17.45/17.67  thf('27', plain, (((r2_hidden @ sk_B_1 @ sk_C) | (v2_struct_0 @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['25', '26'])).
% 17.45/17.67  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 17.45/17.67      inference('clc', [status(thm)], ['27', '28'])).
% 17.45/17.67  thf(d3_xboole_0, axiom,
% 17.45/17.67    (![A:$i,B:$i,C:$i]:
% 17.45/17.67     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 17.45/17.67       ( ![D:$i]:
% 17.45/17.67         ( ( r2_hidden @ D @ C ) <=>
% 17.45/17.67           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 17.45/17.67  thf('30', plain,
% 17.45/17.67      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 17.45/17.67         (~ (r2_hidden @ X3 @ X6)
% 17.45/17.67          | (r2_hidden @ X3 @ X5)
% 17.45/17.67          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 17.45/17.67      inference('cnf', [status(esa)], [d3_xboole_0])).
% 17.45/17.67  thf('31', plain,
% 17.45/17.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 17.45/17.67         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X6))),
% 17.45/17.67      inference('simplify', [status(thm)], ['30'])).
% 17.45/17.67  thf('32', plain,
% 17.45/17.67      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k2_xboole_0 @ sk_C @ X0))),
% 17.45/17.67      inference('sup-', [status(thm)], ['29', '31'])).
% 17.45/17.67  thf('33', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('34', plain,
% 17.45/17.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 17.45/17.67          | (m1_connsp_2 @ X39 @ X38 @ X37)
% 17.45/17.67          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 17.45/17.67          | ~ (l1_pre_topc @ X38)
% 17.45/17.67          | ~ (v2_pre_topc @ X38)
% 17.45/17.67          | (v2_struct_0 @ X38))),
% 17.45/17.67      inference('cnf', [status(esa)], [t21_waybel_9])).
% 17.45/17.67  thf('35', plain,
% 17.45/17.67      (((v2_struct_0 @ sk_A)
% 17.45/17.67        | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67        | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67        | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B_1)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['33', '34'])).
% 17.45/17.67  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('39', plain,
% 17.45/17.67      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B_1))),
% 17.45/17.67      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 17.45/17.67  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('41', plain, ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 17.45/17.67      inference('clc', [status(thm)], ['39', '40'])).
% 17.45/17.67  thf('42', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 17.45/17.67      inference('clc', [status(thm)], ['16', '17'])).
% 17.45/17.67  thf('43', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['41', '42'])).
% 17.45/17.67  thf(t3_subset, axiom,
% 17.45/17.67    (![A:$i,B:$i]:
% 17.45/17.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.45/17.67  thf('44', plain,
% 17.45/17.67      (![X19 : $i, X20 : $i]:
% 17.45/17.67         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 17.45/17.67      inference('cnf', [status(esa)], [t3_subset])).
% 17.45/17.67  thf('45', plain, ((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['43', '44'])).
% 17.45/17.67  thf('46', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['10', '18'])).
% 17.45/17.67  thf('47', plain,
% 17.45/17.67      (![X19 : $i, X20 : $i]:
% 17.45/17.67         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 17.45/17.67      inference('cnf', [status(esa)], [t3_subset])).
% 17.45/17.67  thf('48', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['46', '47'])).
% 17.45/17.67  thf(t8_xboole_1, axiom,
% 17.45/17.67    (![A:$i,B:$i,C:$i]:
% 17.45/17.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.45/17.67       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 17.45/17.67  thf('49', plain,
% 17.45/17.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 17.45/17.67         (~ (r1_tarski @ X9 @ X10)
% 17.45/17.67          | ~ (r1_tarski @ X11 @ X10)
% 17.45/17.67          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 17.45/17.67      inference('cnf', [status(esa)], [t8_xboole_1])).
% 17.45/17.67  thf('50', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))
% 17.45/17.67          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['48', '49'])).
% 17.45/17.67  thf('51', plain,
% 17.45/17.67      ((r1_tarski @ (k2_xboole_0 @ sk_C @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['45', '50'])).
% 17.45/17.67  thf('52', plain,
% 17.45/17.67      (![X19 : $i, X21 : $i]:
% 17.45/17.67         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 17.45/17.67      inference('cnf', [status(esa)], [t3_subset])).
% 17.45/17.67  thf('53', plain,
% 17.45/17.67      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['51', '52'])).
% 17.45/17.67  thf(t39_yellow_6, axiom,
% 17.45/17.67    (![A:$i]:
% 17.45/17.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.45/17.67       ( ![B:$i]:
% 17.45/17.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.45/17.67           ( ![C:$i]:
% 17.45/17.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.45/17.67               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 17.45/17.67                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 17.45/17.67  thf('54', plain,
% 17.45/17.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 17.45/17.67          | ~ (r2_hidden @ X34 @ X36)
% 17.45/17.67          | ~ (v3_pre_topc @ X36 @ X35)
% 17.45/17.67          | (r2_hidden @ X36 @ (u1_struct_0 @ (k9_yellow_6 @ X35 @ X34)))
% 17.45/17.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 17.45/17.67          | ~ (l1_pre_topc @ X35)
% 17.45/17.67          | ~ (v2_pre_topc @ X35)
% 17.45/17.67          | (v2_struct_0 @ X35))),
% 17.45/17.67      inference('cnf', [status(esa)], [t39_yellow_6])).
% 17.45/17.67  thf('55', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v2_struct_0 @ sk_A)
% 17.45/17.67          | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67          | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 17.45/17.67          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 17.45/17.67          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['53', '54'])).
% 17.45/17.67  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('58', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v2_struct_0 @ sk_A)
% 17.45/17.67          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 17.45/17.67          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 17.45/17.67          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('demod', [status(thm)], ['55', '56', '57'])).
% 17.45/17.67  thf('59', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['41', '42'])).
% 17.45/17.67  thf('60', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['10', '18'])).
% 17.45/17.67  thf(fc7_tops_1, axiom,
% 17.45/17.67    (![A:$i,B:$i,C:$i]:
% 17.45/17.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 17.45/17.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 17.45/17.67         ( v3_pre_topc @ C @ A ) & 
% 17.45/17.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.45/17.67       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 17.45/17.67  thf('61', plain,
% 17.45/17.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 17.45/17.67          | ~ (v3_pre_topc @ X25 @ X26)
% 17.45/17.67          | ~ (l1_pre_topc @ X26)
% 17.45/17.67          | ~ (v2_pre_topc @ X26)
% 17.45/17.67          | ~ (v3_pre_topc @ X27 @ X26)
% 17.45/17.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 17.45/17.67          | (v3_pre_topc @ (k2_xboole_0 @ X25 @ X27) @ X26))),
% 17.45/17.67      inference('cnf', [status(esa)], [fc7_tops_1])).
% 17.45/17.67  thf('62', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | ~ (v3_pre_topc @ X0 @ sk_A)
% 17.45/17.67          | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67          | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['60', '61'])).
% 17.45/17.67  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('65', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | ~ (v3_pre_topc @ X0 @ sk_A)
% 17.45/17.67          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['62', '63', '64'])).
% 17.45/17.67  thf(d1_xboole_0, axiom,
% 17.45/17.67    (![A:$i]:
% 17.45/17.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 17.45/17.67  thf('66', plain,
% 17.45/17.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 17.45/17.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 17.45/17.67  thf('67', plain,
% 17.45/17.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 17.45/17.67         (~ (r2_hidden @ X7 @ X5)
% 17.45/17.67          | (r2_hidden @ X7 @ X6)
% 17.45/17.67          | (r2_hidden @ X7 @ X4)
% 17.45/17.67          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 17.45/17.67      inference('cnf', [status(esa)], [d3_xboole_0])).
% 17.45/17.67  thf('68', plain,
% 17.45/17.67      (![X4 : $i, X6 : $i, X7 : $i]:
% 17.45/17.67         ((r2_hidden @ X7 @ X4)
% 17.45/17.67          | (r2_hidden @ X7 @ X6)
% 17.45/17.67          | ~ (r2_hidden @ X7 @ (k2_xboole_0 @ X6 @ X4)))),
% 17.45/17.67      inference('simplify', [status(thm)], ['67'])).
% 17.45/17.67  thf('69', plain,
% 17.45/17.67      (![X0 : $i, X1 : $i]:
% 17.45/17.67         ((v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 17.45/17.67          | (r2_hidden @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 17.45/17.67          | (r2_hidden @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 17.45/17.67      inference('sup-', [status(thm)], ['66', '68'])).
% 17.45/17.67  thf('70', plain,
% 17.45/17.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 17.45/17.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 17.45/17.67  thf('71', plain,
% 17.45/17.67      (![X0 : $i, X1 : $i]:
% 17.45/17.67         ((r2_hidden @ (sk_B @ (k2_xboole_0 @ X0 @ X1)) @ X1)
% 17.45/17.67          | (v1_xboole_0 @ (k2_xboole_0 @ X0 @ X1))
% 17.45/17.67          | ~ (v1_xboole_0 @ X0))),
% 17.45/17.67      inference('sup-', [status(thm)], ['69', '70'])).
% 17.45/17.67  thf('72', plain,
% 17.45/17.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 17.45/17.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 17.45/17.67  thf('73', plain,
% 17.45/17.67      (![X0 : $i, X1 : $i]:
% 17.45/17.67         (~ (v1_xboole_0 @ X1)
% 17.45/17.67          | (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 17.45/17.67          | ~ (v1_xboole_0 @ X0))),
% 17.45/17.67      inference('sup-', [status(thm)], ['71', '72'])).
% 17.45/17.67  thf('74', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf(d2_subset_1, axiom,
% 17.45/17.67    (![A:$i,B:$i]:
% 17.45/17.67     ( ( ( v1_xboole_0 @ A ) =>
% 17.45/17.67         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 17.45/17.67       ( ( ~( v1_xboole_0 @ A ) ) =>
% 17.45/17.67         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 17.45/17.67  thf('75', plain,
% 17.45/17.67      (![X14 : $i, X15 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X14 @ X15)
% 17.45/17.67          | (r2_hidden @ X14 @ X15)
% 17.45/17.67          | (v1_xboole_0 @ X15))),
% 17.45/17.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 17.45/17.67  thf('76', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('sup-', [status(thm)], ['74', '75'])).
% 17.45/17.67  thf('77', plain,
% 17.45/17.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 17.45/17.67          | ~ (r2_hidden @ X36 @ (u1_struct_0 @ (k9_yellow_6 @ X35 @ X34)))
% 17.45/17.67          | (v3_pre_topc @ X36 @ X35)
% 17.45/17.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 17.45/17.67          | ~ (l1_pre_topc @ X35)
% 17.45/17.67          | ~ (v2_pre_topc @ X35)
% 17.45/17.67          | (v2_struct_0 @ X35))),
% 17.45/17.67      inference('cnf', [status(esa)], [t39_yellow_6])).
% 17.45/17.67  thf('78', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A)
% 17.45/17.67        | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67        | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67        | (v3_pre_topc @ sk_C @ sk_A)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['76', '77'])).
% 17.45/17.67  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('81', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('82', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67        | (v3_pre_topc @ sk_C @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 17.45/17.67  thf('83', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['10', '18'])).
% 17.45/17.67  thf('84', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A)
% 17.45/17.67        | (v3_pre_topc @ sk_C @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['82', '83'])).
% 17.45/17.67  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('86', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_C @ sk_A)
% 17.45/17.67        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('clc', [status(thm)], ['84', '85'])).
% 17.45/17.67  thf('87', plain,
% 17.45/17.67      (![X15 : $i, X16 : $i]:
% 17.45/17.67         (~ (v1_xboole_0 @ X16)
% 17.45/17.67          | (m1_subset_1 @ X16 @ X15)
% 17.45/17.67          | ~ (v1_xboole_0 @ X15))),
% 17.45/17.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 17.45/17.67  thf('88', plain,
% 17.45/17.67      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('89', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | ~ (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['87', '88'])).
% 17.45/17.67  thf('90', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_C @ sk_A)
% 17.45/17.67        | ~ (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['86', '89'])).
% 17.45/17.67  thf('91', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ sk_D_1)
% 17.45/17.67        | ~ (v1_xboole_0 @ sk_C)
% 17.45/17.67        | (v3_pre_topc @ sk_C @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['73', '90'])).
% 17.45/17.67  thf('92', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_C @ sk_A)
% 17.45/17.67        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('clc', [status(thm)], ['84', '85'])).
% 17.45/17.67  thf('93', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('94', plain,
% 17.45/17.67      (![X15 : $i, X16 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X16 @ X15)
% 17.45/17.67          | (v1_xboole_0 @ X16)
% 17.45/17.67          | ~ (v1_xboole_0 @ X15))),
% 17.45/17.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 17.45/17.67  thf('95', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v1_xboole_0 @ sk_D_1))),
% 17.45/17.67      inference('sup-', [status(thm)], ['93', '94'])).
% 17.45/17.67  thf('96', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 17.45/17.67      inference('sup-', [status(thm)], ['92', '95'])).
% 17.45/17.67  thf('97', plain, (((v3_pre_topc @ sk_C @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 17.45/17.67      inference('clc', [status(thm)], ['91', '96'])).
% 17.45/17.67  thf('98', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_C @ sk_A)
% 17.45/17.67        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('clc', [status(thm)], ['84', '85'])).
% 17.45/17.67  thf('99', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('100', plain,
% 17.45/17.67      (![X15 : $i, X16 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X16 @ X15)
% 17.45/17.67          | (v1_xboole_0 @ X16)
% 17.45/17.67          | ~ (v1_xboole_0 @ X15))),
% 17.45/17.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 17.45/17.67  thf('101', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v1_xboole_0 @ sk_C))),
% 17.45/17.67      inference('sup-', [status(thm)], ['99', '100'])).
% 17.45/17.67  thf('102', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 17.45/17.67      inference('sup-', [status(thm)], ['98', '101'])).
% 17.45/17.67  thf('103', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 17.45/17.67      inference('clc', [status(thm)], ['97', '102'])).
% 17.45/17.67  thf('104', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['65', '103'])).
% 17.45/17.67  thf('105', plain,
% 17.45/17.67      ((~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 17.45/17.67        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['59', '104'])).
% 17.45/17.67  thf('106', plain,
% 17.45/17.67      (![X0 : $i, X1 : $i]:
% 17.45/17.67         (~ (v1_xboole_0 @ X1)
% 17.45/17.67          | (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 17.45/17.67          | ~ (v1_xboole_0 @ X0))),
% 17.45/17.67      inference('sup-', [status(thm)], ['71', '72'])).
% 17.45/17.67  thf('107', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('108', plain,
% 17.45/17.67      (![X14 : $i, X15 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X14 @ X15)
% 17.45/17.67          | (r2_hidden @ X14 @ X15)
% 17.45/17.67          | (v1_xboole_0 @ X15))),
% 17.45/17.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 17.45/17.67  thf('109', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('sup-', [status(thm)], ['107', '108'])).
% 17.45/17.67  thf('110', plain,
% 17.45/17.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 17.45/17.67         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 17.45/17.67          | ~ (r2_hidden @ X36 @ (u1_struct_0 @ (k9_yellow_6 @ X35 @ X34)))
% 17.45/17.67          | (v3_pre_topc @ X36 @ X35)
% 17.45/17.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 17.45/17.67          | ~ (l1_pre_topc @ X35)
% 17.45/17.67          | ~ (v2_pre_topc @ X35)
% 17.45/17.67          | (v2_struct_0 @ X35))),
% 17.45/17.67      inference('cnf', [status(esa)], [t39_yellow_6])).
% 17.45/17.67  thf('111', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A)
% 17.45/17.67        | ~ (v2_pre_topc @ sk_A)
% 17.45/17.67        | ~ (l1_pre_topc @ sk_A)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67        | (v3_pre_topc @ sk_D_1 @ sk_A)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['109', '110'])).
% 17.45/17.67  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('114', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('115', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A)
% 17.45/17.67        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.45/17.67        | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 17.45/17.67  thf('116', plain,
% 17.45/17.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['41', '42'])).
% 17.45/17.67  thf('117', plain,
% 17.45/17.67      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A)
% 17.45/17.67        | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['115', '116'])).
% 17.45/17.67  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('119', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 17.45/17.67        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('clc', [status(thm)], ['117', '118'])).
% 17.45/17.67  thf('120', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | ~ (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['87', '88'])).
% 17.45/17.67  thf('121', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 17.45/17.67        | ~ (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['119', '120'])).
% 17.45/17.67  thf('122', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ sk_D_1)
% 17.45/17.67        | ~ (v1_xboole_0 @ sk_C)
% 17.45/17.67        | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['106', '121'])).
% 17.45/17.67  thf('123', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 17.45/17.67        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('clc', [status(thm)], ['117', '118'])).
% 17.45/17.67  thf('124', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v1_xboole_0 @ sk_D_1))),
% 17.45/17.67      inference('sup-', [status(thm)], ['93', '94'])).
% 17.45/17.67  thf('125', plain, (((v3_pre_topc @ sk_D_1 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 17.45/17.67      inference('sup-', [status(thm)], ['123', '124'])).
% 17.45/17.67  thf('126', plain, (((v3_pre_topc @ sk_D_1 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 17.45/17.67      inference('clc', [status(thm)], ['122', '125'])).
% 17.45/17.67  thf('127', plain,
% 17.45/17.67      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 17.45/17.67        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 17.45/17.67      inference('clc', [status(thm)], ['117', '118'])).
% 17.45/17.67  thf('128', plain,
% 17.45/17.67      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v1_xboole_0 @ sk_C))),
% 17.45/17.67      inference('sup-', [status(thm)], ['99', '100'])).
% 17.45/17.67  thf('129', plain, (((v3_pre_topc @ sk_D_1 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 17.45/17.67      inference('sup-', [status(thm)], ['127', '128'])).
% 17.45/17.67  thf('130', plain, ((v3_pre_topc @ sk_D_1 @ sk_A)),
% 17.45/17.67      inference('clc', [status(thm)], ['126', '129'])).
% 17.45/17.67  thf('131', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)),
% 17.45/17.67      inference('demod', [status(thm)], ['105', '130'])).
% 17.45/17.67  thf('132', plain,
% 17.45/17.67      (![X0 : $i]:
% 17.45/17.67         ((v2_struct_0 @ sk_A)
% 17.45/17.67          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 17.45/17.67          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 17.45/17.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 17.45/17.67      inference('demod', [status(thm)], ['58', '131'])).
% 17.45/17.67  thf('133', plain,
% 17.45/17.67      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 17.45/17.67        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A))),
% 17.45/17.67      inference('sup-', [status(thm)], ['32', '132'])).
% 17.45/17.67  thf('134', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('135', plain,
% 17.45/17.67      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 17.45/17.67        | (v2_struct_0 @ sk_A))),
% 17.45/17.67      inference('demod', [status(thm)], ['133', '134'])).
% 17.45/17.67  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 17.45/17.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.45/17.67  thf('137', plain,
% 17.45/17.67      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('clc', [status(thm)], ['135', '136'])).
% 17.45/17.67  thf(t1_subset, axiom,
% 17.45/17.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 17.45/17.67  thf('138', plain,
% 17.45/17.67      (![X17 : $i, X18 : $i]:
% 17.45/17.67         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 17.45/17.67      inference('cnf', [status(esa)], [t1_subset])).
% 17.45/17.67  thf('139', plain,
% 17.45/17.67      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 17.45/17.67        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 17.45/17.67      inference('sup-', [status(thm)], ['137', '138'])).
% 17.45/17.67  thf('140', plain, ($false), inference('demod', [status(thm)], ['0', '139'])).
% 17.45/17.67  
% 17.45/17.67  % SZS output end Refutation
% 17.45/17.67  
% 17.45/17.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
