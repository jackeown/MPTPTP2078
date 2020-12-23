%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pnn1JlPNdW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:27 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 600 expanded)
%              Number of leaves         :   32 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          : 1290 (10541 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ( m1_connsp_2 @ X42 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
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
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_connsp_2 @ X33 @ X31 @ X32 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_D )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 ) ) ),
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
      | ( r2_hidden @ X0 @ sk_D )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_D ),
    inference(clc,[status(thm)],['27','28'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ( m1_connsp_2 @ X42 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','55'])).

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

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ~ ( v3_pre_topc @ X39 @ X38 )
      | ( r2_hidden @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,
    ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('101',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ) ),
    inference(clc,[status(thm)],['86','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('105',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['43','44'])).

thf('112',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['112','113'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['102','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','117'])).

thf('119',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('124',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('125',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pnn1JlPNdW
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.81/3.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.81/3.05  % Solved by: fo/fo7.sh
% 2.81/3.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.81/3.05  % done 2953 iterations in 2.575s
% 2.81/3.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.81/3.05  % SZS output start Refutation
% 2.81/3.05  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.81/3.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.81/3.05  thf(sk_D_type, type, sk_D: $i).
% 2.81/3.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.81/3.05  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.81/3.05  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 2.81/3.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.81/3.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.81/3.05  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.81/3.05  thf(sk_A_type, type, sk_A: $i).
% 2.81/3.05  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.81/3.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.81/3.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.81/3.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.81/3.05  thf(sk_C_type, type, sk_C: $i).
% 2.81/3.05  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 2.81/3.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.81/3.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.81/3.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.81/3.05  thf(t23_waybel_9, conjecture,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.81/3.05       ( ![B:$i]:
% 2.81/3.05         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.81/3.05           ( ![C:$i]:
% 2.81/3.05             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.81/3.05               ( ![D:$i]:
% 2.81/3.05                 ( ( m1_subset_1 @
% 2.81/3.05                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.81/3.05                   ( m1_subset_1 @
% 2.81/3.05                     ( k2_xboole_0 @ C @ D ) @ 
% 2.81/3.05                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 2.81/3.05  thf(zf_stmt_0, negated_conjecture,
% 2.81/3.05    (~( ![A:$i]:
% 2.81/3.05        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.81/3.05            ( l1_pre_topc @ A ) ) =>
% 2.81/3.05          ( ![B:$i]:
% 2.81/3.05            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.81/3.05              ( ![C:$i]:
% 2.81/3.05                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.81/3.05                  ( ![D:$i]:
% 2.81/3.05                    ( ( m1_subset_1 @
% 2.81/3.05                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.81/3.05                      ( m1_subset_1 @
% 2.81/3.05                        ( k2_xboole_0 @ C @ D ) @ 
% 2.81/3.05                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 2.81/3.05    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 2.81/3.05  thf('0', plain,
% 2.81/3.05      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('2', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(t21_waybel_9, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.81/3.05       ( ![B:$i]:
% 2.81/3.05         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.81/3.05           ( ![C:$i]:
% 2.81/3.05             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.81/3.05               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 2.81/3.05  thf('3', plain,
% 2.81/3.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 2.81/3.05          | (m1_connsp_2 @ X42 @ X41 @ X40)
% 2.81/3.05          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 2.81/3.05          | ~ (l1_pre_topc @ X41)
% 2.81/3.05          | ~ (v2_pre_topc @ X41)
% 2.81/3.05          | (v2_struct_0 @ X41))),
% 2.81/3.05      inference('cnf', [status(esa)], [t21_waybel_9])).
% 2.81/3.05  thf('4', plain,
% 2.81/3.05      (((v2_struct_0 @ sk_A)
% 2.81/3.05        | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05        | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05        | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['2', '3'])).
% 2.81/3.05  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('8', plain,
% 2.81/3.05      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1))),
% 2.81/3.05      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.81/3.05  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('10', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.81/3.05      inference('clc', [status(thm)], ['8', '9'])).
% 2.81/3.05  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(dt_m1_connsp_2, axiom,
% 2.81/3.05    (![A:$i,B:$i]:
% 2.81/3.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.81/3.05         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 2.81/3.05       ( ![C:$i]:
% 2.81/3.05         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 2.81/3.05           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.81/3.05  thf('12', plain,
% 2.81/3.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.81/3.05         (~ (l1_pre_topc @ X31)
% 2.81/3.05          | ~ (v2_pre_topc @ X31)
% 2.81/3.05          | (v2_struct_0 @ X31)
% 2.81/3.05          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 2.81/3.05          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.81/3.05          | ~ (m1_connsp_2 @ X33 @ X31 @ X32))),
% 2.81/3.05      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 2.81/3.05  thf('13', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 2.81/3.05          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | (v2_struct_0 @ sk_A)
% 2.81/3.05          | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05          | ~ (l1_pre_topc @ sk_A))),
% 2.81/3.05      inference('sup-', [status(thm)], ['11', '12'])).
% 2.81/3.05  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('16', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 2.81/3.05          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['13', '14', '15'])).
% 2.81/3.05  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('18', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 2.81/3.05      inference('clc', [status(thm)], ['16', '17'])).
% 2.81/3.05  thf('19', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['10', '18'])).
% 2.81/3.05  thf(t6_connsp_2, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.81/3.05       ( ![B:$i]:
% 2.81/3.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.81/3.05           ( ![C:$i]:
% 2.81/3.05             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.81/3.05               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.81/3.05  thf('20', plain,
% 2.81/3.05      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.81/3.05          | ~ (m1_connsp_2 @ X34 @ X35 @ X36)
% 2.81/3.05          | (r2_hidden @ X36 @ X34)
% 2.81/3.05          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 2.81/3.05          | ~ (l1_pre_topc @ X35)
% 2.81/3.05          | ~ (v2_pre_topc @ X35)
% 2.81/3.05          | (v2_struct_0 @ X35))),
% 2.81/3.05      inference('cnf', [status(esa)], [t6_connsp_2])).
% 2.81/3.05  thf('21', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v2_struct_0 @ sk_A)
% 2.81/3.05          | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05          | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.81/3.05          | (r2_hidden @ X0 @ sk_D)
% 2.81/3.05          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0))),
% 2.81/3.05      inference('sup-', [status(thm)], ['19', '20'])).
% 2.81/3.05  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('24', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v2_struct_0 @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.81/3.05          | (r2_hidden @ X0 @ sk_D)
% 2.81/3.05          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0))),
% 2.81/3.05      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.81/3.05  thf('25', plain,
% 2.81/3.05      ((~ (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 2.81/3.05        | (r2_hidden @ sk_B_1 @ sk_D)
% 2.81/3.05        | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('sup-', [status(thm)], ['1', '24'])).
% 2.81/3.05  thf('26', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.81/3.05      inference('clc', [status(thm)], ['8', '9'])).
% 2.81/3.05  thf('27', plain, (((r2_hidden @ sk_B_1 @ sk_D) | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['25', '26'])).
% 2.81/3.05  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_D)),
% 2.81/3.05      inference('clc', [status(thm)], ['27', '28'])).
% 2.81/3.05  thf(l1_zfmisc_1, axiom,
% 2.81/3.05    (![A:$i,B:$i]:
% 2.81/3.05     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.81/3.05  thf('30', plain,
% 2.81/3.05      (![X7 : $i, X9 : $i]:
% 2.81/3.05         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 2.81/3.05      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.81/3.05  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_D)),
% 2.81/3.05      inference('sup-', [status(thm)], ['29', '30'])).
% 2.81/3.05  thf(t10_xboole_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.81/3.05  thf('32', plain,
% 2.81/3.05      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.81/3.05         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 2.81/3.05      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.81/3.05  thf('33', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (r1_tarski @ (k1_tarski @ sk_B_1) @ (k2_xboole_0 @ X0 @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['31', '32'])).
% 2.81/3.05  thf('34', plain,
% 2.81/3.05      (![X7 : $i, X8 : $i]:
% 2.81/3.05         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 2.81/3.05      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.81/3.05  thf('35', plain,
% 2.81/3.05      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k2_xboole_0 @ X0 @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['33', '34'])).
% 2.81/3.05  thf('36', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['10', '18'])).
% 2.81/3.05  thf('37', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('38', plain,
% 2.81/3.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 2.81/3.05          | (m1_connsp_2 @ X42 @ X41 @ X40)
% 2.81/3.05          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 2.81/3.05          | ~ (l1_pre_topc @ X41)
% 2.81/3.05          | ~ (v2_pre_topc @ X41)
% 2.81/3.05          | (v2_struct_0 @ X41))),
% 2.81/3.05      inference('cnf', [status(esa)], [t21_waybel_9])).
% 2.81/3.05  thf('39', plain,
% 2.81/3.05      (((v2_struct_0 @ sk_A)
% 2.81/3.05        | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05        | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['37', '38'])).
% 2.81/3.05  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('42', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('43', plain,
% 2.81/3.05      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 2.81/3.05      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 2.81/3.05  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('45', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.81/3.05      inference('clc', [status(thm)], ['43', '44'])).
% 2.81/3.05  thf('46', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 2.81/3.05      inference('clc', [status(thm)], ['16', '17'])).
% 2.81/3.05  thf('47', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['45', '46'])).
% 2.81/3.05  thf(dt_k4_subset_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.81/3.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.81/3.05       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.81/3.05  thf('48', plain,
% 2.81/3.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 2.81/3.05          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 2.81/3.05          | (m1_subset_1 @ (k4_subset_1 @ X16 @ X15 @ X17) @ 
% 2.81/3.05             (k1_zfmisc_1 @ X16)))),
% 2.81/3.05      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.81/3.05  thf('49', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 2.81/3.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.81/3.05      inference('sup-', [status(thm)], ['47', '48'])).
% 2.81/3.05  thf('50', plain,
% 2.81/3.05      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 2.81/3.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['36', '49'])).
% 2.81/3.05  thf('51', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['10', '18'])).
% 2.81/3.05  thf('52', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['45', '46'])).
% 2.81/3.05  thf(redefinition_k4_subset_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.81/3.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.81/3.05       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.81/3.05  thf('53', plain,
% 2.81/3.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.81/3.05          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 2.81/3.05          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.81/3.05  thf('54', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 2.81/3.05            = (k2_xboole_0 @ sk_C @ X0))
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.81/3.05      inference('sup-', [status(thm)], ['52', '53'])).
% 2.81/3.05  thf('55', plain,
% 2.81/3.05      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 2.81/3.05         = (k2_xboole_0 @ sk_C @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['51', '54'])).
% 2.81/3.05  thf('56', plain,
% 2.81/3.05      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('demod', [status(thm)], ['50', '55'])).
% 2.81/3.05  thf(t39_yellow_6, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.81/3.05       ( ![B:$i]:
% 2.81/3.05         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.81/3.05           ( ![C:$i]:
% 2.81/3.05             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.81/3.05               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 2.81/3.05                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.81/3.05  thf('57', plain,
% 2.81/3.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 2.81/3.05          | ~ (r2_hidden @ X37 @ X39)
% 2.81/3.05          | ~ (v3_pre_topc @ X39 @ X38)
% 2.81/3.05          | (r2_hidden @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 2.81/3.05          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 2.81/3.05          | ~ (l1_pre_topc @ X38)
% 2.81/3.05          | ~ (v2_pre_topc @ X38)
% 2.81/3.05          | (v2_struct_0 @ X38))),
% 2.81/3.05      inference('cnf', [status(esa)], [t39_yellow_6])).
% 2.81/3.05  thf('58', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v2_struct_0 @ sk_A)
% 2.81/3.05          | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05          | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.81/3.05          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 2.81/3.05          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['56', '57'])).
% 2.81/3.05  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('61', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['10', '18'])).
% 2.81/3.05  thf('62', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(d2_subset_1, axiom,
% 2.81/3.05    (![A:$i,B:$i]:
% 2.81/3.05     ( ( ( v1_xboole_0 @ A ) =>
% 2.81/3.05         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.81/3.05       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.81/3.05         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.81/3.05  thf('63', plain,
% 2.81/3.05      (![X12 : $i, X13 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X12 @ X13)
% 2.81/3.05          | (r2_hidden @ X12 @ X13)
% 2.81/3.05          | (v1_xboole_0 @ X13))),
% 2.81/3.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.81/3.05  thf('64', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 2.81/3.05      inference('sup-', [status(thm)], ['62', '63'])).
% 2.81/3.05  thf('65', plain,
% 2.81/3.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 2.81/3.05          | ~ (r2_hidden @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 2.81/3.05          | (v3_pre_topc @ X39 @ X38)
% 2.81/3.05          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 2.81/3.05          | ~ (l1_pre_topc @ X38)
% 2.81/3.05          | ~ (v2_pre_topc @ X38)
% 2.81/3.05          | (v2_struct_0 @ X38))),
% 2.81/3.05      inference('cnf', [status(esa)], [t39_yellow_6])).
% 2.81/3.05  thf('66', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A)
% 2.81/3.05        | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05        | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05        | (v3_pre_topc @ sk_C @ sk_A)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['64', '65'])).
% 2.81/3.05  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('69', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('70', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05        | (v3_pre_topc @ sk_C @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 2.81/3.05  thf('71', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['45', '46'])).
% 2.81/3.05  thf('72', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A)
% 2.81/3.05        | (v3_pre_topc @ sk_C @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['70', '71'])).
% 2.81/3.05  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('74', plain,
% 2.81/3.05      (((v3_pre_topc @ sk_C @ sk_A)
% 2.81/3.05        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 2.81/3.05      inference('clc', [status(thm)], ['72', '73'])).
% 2.81/3.05  thf('75', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('76', plain,
% 2.81/3.05      (![X13 : $i, X14 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X14 @ X13)
% 2.81/3.05          | (v1_xboole_0 @ X14)
% 2.81/3.05          | ~ (v1_xboole_0 @ X13))),
% 2.81/3.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.81/3.05  thf('77', plain,
% 2.81/3.05      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v1_xboole_0 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['75', '76'])).
% 2.81/3.05  thf('78', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['74', '77'])).
% 2.81/3.05  thf('79', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['45', '46'])).
% 2.81/3.05  thf(fc7_tops_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 2.81/3.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 2.81/3.05         ( v3_pre_topc @ C @ A ) & 
% 2.81/3.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.81/3.05       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 2.81/3.05  thf('80', plain,
% 2.81/3.05      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.81/3.05          | ~ (v3_pre_topc @ X28 @ X29)
% 2.81/3.05          | ~ (l1_pre_topc @ X29)
% 2.81/3.05          | ~ (v2_pre_topc @ X29)
% 2.81/3.05          | ~ (v3_pre_topc @ X30 @ X29)
% 2.81/3.05          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.81/3.05          | (v3_pre_topc @ (k2_xboole_0 @ X28 @ X30) @ X29))),
% 2.81/3.05      inference('cnf', [status(esa)], [fc7_tops_1])).
% 2.81/3.05  thf('81', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.81/3.05          | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05          | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 2.81/3.05      inference('sup-', [status(thm)], ['79', '80'])).
% 2.81/3.05  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('84', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.81/3.05          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['81', '82', '83'])).
% 2.81/3.05  thf('85', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v1_xboole_0 @ sk_C)
% 2.81/3.05          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05          | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A))),
% 2.81/3.05      inference('sup-', [status(thm)], ['78', '84'])).
% 2.81/3.05  thf('86', plain,
% 2.81/3.05      (((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 2.81/3.05        | ~ (v3_pre_topc @ sk_D @ sk_A)
% 2.81/3.05        | (v1_xboole_0 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['61', '85'])).
% 2.81/3.05  thf('87', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('88', plain,
% 2.81/3.05      (![X12 : $i, X13 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X12 @ X13)
% 2.81/3.05          | (r2_hidden @ X12 @ X13)
% 2.81/3.05          | (v1_xboole_0 @ X13))),
% 2.81/3.05      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.81/3.05  thf('89', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (r2_hidden @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 2.81/3.05      inference('sup-', [status(thm)], ['87', '88'])).
% 2.81/3.05  thf('90', plain,
% 2.81/3.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 2.81/3.05          | ~ (r2_hidden @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 2.81/3.05          | (v3_pre_topc @ X39 @ X38)
% 2.81/3.05          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 2.81/3.05          | ~ (l1_pre_topc @ X38)
% 2.81/3.05          | ~ (v2_pre_topc @ X38)
% 2.81/3.05          | (v2_struct_0 @ X38))),
% 2.81/3.05      inference('cnf', [status(esa)], [t39_yellow_6])).
% 2.81/3.05  thf('91', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A)
% 2.81/3.05        | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05        | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05        | (v3_pre_topc @ sk_D @ sk_A)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['89', '90'])).
% 2.81/3.05  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('94', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('95', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A)
% 2.81/3.05        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.81/3.05        | (v3_pre_topc @ sk_D @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 2.81/3.05  thf('96', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['10', '18'])).
% 2.81/3.05  thf('97', plain,
% 2.81/3.05      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A)
% 2.81/3.05        | (v3_pre_topc @ sk_D @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['95', '96'])).
% 2.81/3.05  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('99', plain,
% 2.81/3.05      (((v3_pre_topc @ sk_D @ sk_A)
% 2.81/3.05        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 2.81/3.05      inference('clc', [status(thm)], ['97', '98'])).
% 2.81/3.05  thf('100', plain,
% 2.81/3.05      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v1_xboole_0 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['75', '76'])).
% 2.81/3.05  thf('101', plain, (((v3_pre_topc @ sk_D @ sk_A) | (v1_xboole_0 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['99', '100'])).
% 2.81/3.05  thf('102', plain,
% 2.81/3.05      (((v1_xboole_0 @ sk_C)
% 2.81/3.05        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A))),
% 2.81/3.05      inference('clc', [status(thm)], ['86', '101'])).
% 2.81/3.05  thf('103', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('104', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['45', '46'])).
% 2.81/3.05  thf('105', plain,
% 2.81/3.05      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.81/3.05          | ~ (m1_connsp_2 @ X34 @ X35 @ X36)
% 2.81/3.05          | (r2_hidden @ X36 @ X34)
% 2.81/3.05          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 2.81/3.05          | ~ (l1_pre_topc @ X35)
% 2.81/3.05          | ~ (v2_pre_topc @ X35)
% 2.81/3.05          | (v2_struct_0 @ X35))),
% 2.81/3.05      inference('cnf', [status(esa)], [t6_connsp_2])).
% 2.81/3.05  thf('106', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v2_struct_0 @ sk_A)
% 2.81/3.05          | ~ (v2_pre_topc @ sk_A)
% 2.81/3.05          | ~ (l1_pre_topc @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.81/3.05          | (r2_hidden @ X0 @ sk_C)
% 2.81/3.05          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 2.81/3.05      inference('sup-', [status(thm)], ['104', '105'])).
% 2.81/3.05  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('109', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v2_struct_0 @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.81/3.05          | (r2_hidden @ X0 @ sk_C)
% 2.81/3.05          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 2.81/3.05      inference('demod', [status(thm)], ['106', '107', '108'])).
% 2.81/3.05  thf('110', plain,
% 2.81/3.05      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 2.81/3.05        | (r2_hidden @ sk_B_1 @ sk_C)
% 2.81/3.05        | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('sup-', [status(thm)], ['103', '109'])).
% 2.81/3.05  thf('111', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.81/3.05      inference('clc', [status(thm)], ['43', '44'])).
% 2.81/3.05  thf('112', plain, (((r2_hidden @ sk_B_1 @ sk_C) | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['110', '111'])).
% 2.81/3.05  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('114', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 2.81/3.05      inference('clc', [status(thm)], ['112', '113'])).
% 2.81/3.05  thf(d1_xboole_0, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.81/3.05  thf('115', plain,
% 2.81/3.05      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.81/3.05      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.81/3.05  thf('116', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.81/3.05      inference('sup-', [status(thm)], ['114', '115'])).
% 2.81/3.05  thf('117', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)),
% 2.81/3.05      inference('clc', [status(thm)], ['102', '116'])).
% 2.81/3.05  thf('118', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         ((v2_struct_0 @ sk_A)
% 2.81/3.05          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.81/3.05          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.81/3.05      inference('demod', [status(thm)], ['58', '59', '60', '117'])).
% 2.81/3.05  thf('119', plain,
% 2.81/3.05      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 2.81/3.05        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('sup-', [status(thm)], ['35', '118'])).
% 2.81/3.05  thf('120', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('121', plain,
% 2.81/3.05      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 2.81/3.05        | (v2_struct_0 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['119', '120'])).
% 2.81/3.05  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('123', plain,
% 2.81/3.05      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('clc', [status(thm)], ['121', '122'])).
% 2.81/3.05  thf(t1_subset, axiom,
% 2.81/3.05    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.81/3.05  thf('124', plain,
% 2.81/3.05      (![X21 : $i, X22 : $i]:
% 2.81/3.05         ((m1_subset_1 @ X21 @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 2.81/3.05      inference('cnf', [status(esa)], [t1_subset])).
% 2.81/3.05  thf('125', plain,
% 2.81/3.05      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 2.81/3.05        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['123', '124'])).
% 2.81/3.05  thf('126', plain, ($false), inference('demod', [status(thm)], ['0', '125'])).
% 2.81/3.05  
% 2.81/3.05  % SZS output end Refutation
% 2.81/3.05  
% 2.81/3.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
