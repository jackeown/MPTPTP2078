%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3cuK3ofQJX

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:28 EST 2020

% Result     : Theorem 38.48s
% Output     : Refutation 38.48s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 688 expanded)
%              Number of leaves         :   32 ( 209 expanded)
%              Depth                    :   22
%              Number of atoms          : 1247 (12050 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X40 ) )
      | ( m1_connsp_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ ( k9_yellow_6 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_connsp_2 @ X32 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
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
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_connsp_2 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_B @ sk_C ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X40 ) )
      | ( m1_connsp_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ ( k9_yellow_6 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','52'])).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r2_hidden @ X36 @ X38 )
      | ~ ( v3_pre_topc @ X38 @ X37 )
      | ( r2_hidden @ X38 @ ( u1_struct_0 @ ( k9_yellow_6 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X27 @ X29 ) @ X28 ) ) ),
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

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r2_hidden @ X38 @ ( u1_struct_0 @ ( k9_yellow_6 @ X37 @ X36 ) ) )
      | ( v3_pre_topc @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('84',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('85',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('86',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('87',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','90'])).

thf('92',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r2_hidden @ X38 @ ( u1_struct_0 @ ( k9_yellow_6 @ X37 @ X36 ) ) )
      | ( v3_pre_topc @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('107',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('109',plain,(
    v3_pre_topc @ sk_D_1 @ sk_A ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['92','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('117',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('118',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3cuK3ofQJX
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:03:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 38.48/38.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 38.48/38.69  % Solved by: fo/fo7.sh
% 38.48/38.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.48/38.69  % done 20774 iterations in 38.224s
% 38.48/38.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 38.48/38.69  % SZS output start Refutation
% 38.48/38.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.48/38.69  thf(sk_A_type, type, sk_A: $i).
% 38.48/38.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 38.48/38.69  thf(sk_C_type, type, sk_C: $i).
% 38.48/38.69  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 38.48/38.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 38.48/38.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 38.48/38.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 38.48/38.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 38.48/38.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 38.48/38.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 38.48/38.69  thf(sk_B_type, type, sk_B: $i).
% 38.48/38.69  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 38.48/38.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 38.48/38.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 38.48/38.69  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 38.48/38.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 38.48/38.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 38.48/38.69  thf(t23_waybel_9, conjecture,
% 38.48/38.69    (![A:$i]:
% 38.48/38.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 38.48/38.69       ( ![B:$i]:
% 38.48/38.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 38.48/38.69           ( ![C:$i]:
% 38.48/38.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 38.48/38.69               ( ![D:$i]:
% 38.48/38.69                 ( ( m1_subset_1 @
% 38.48/38.69                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 38.48/38.69                   ( m1_subset_1 @
% 38.48/38.69                     ( k2_xboole_0 @ C @ D ) @ 
% 38.48/38.69                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 38.48/38.69  thf(zf_stmt_0, negated_conjecture,
% 38.48/38.69    (~( ![A:$i]:
% 38.48/38.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 38.48/38.69            ( l1_pre_topc @ A ) ) =>
% 38.48/38.69          ( ![B:$i]:
% 38.48/38.69            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 38.48/38.69              ( ![C:$i]:
% 38.48/38.69                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 38.48/38.69                  ( ![D:$i]:
% 38.48/38.69                    ( ( m1_subset_1 @
% 38.48/38.69                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 38.48/38.69                      ( m1_subset_1 @
% 38.48/38.69                        ( k2_xboole_0 @ C @ D ) @ 
% 38.48/38.69                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 38.48/38.69    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 38.48/38.69  thf('0', plain,
% 38.48/38.69      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('2', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf(t21_waybel_9, axiom,
% 38.48/38.69    (![A:$i]:
% 38.48/38.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 38.48/38.69       ( ![B:$i]:
% 38.48/38.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 38.48/38.69           ( ![C:$i]:
% 38.48/38.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 38.48/38.69               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 38.48/38.69  thf('3', plain,
% 38.48/38.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X40))
% 38.48/38.69          | (m1_connsp_2 @ X41 @ X40 @ X39)
% 38.48/38.69          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ (k9_yellow_6 @ X40 @ X39)))
% 38.48/38.69          | ~ (l1_pre_topc @ X40)
% 38.48/38.69          | ~ (v2_pre_topc @ X40)
% 38.48/38.69          | (v2_struct_0 @ X40))),
% 38.48/38.69      inference('cnf', [status(esa)], [t21_waybel_9])).
% 38.48/38.69  thf('4', plain,
% 38.48/38.69      (((v2_struct_0 @ sk_A)
% 38.48/38.69        | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69        | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['2', '3'])).
% 38.48/38.69  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('7', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('8', plain,
% 38.48/38.69      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 38.48/38.69      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 38.48/38.69  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('10', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 38.48/38.69      inference('clc', [status(thm)], ['8', '9'])).
% 38.48/38.69  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf(dt_m1_connsp_2, axiom,
% 38.48/38.69    (![A:$i,B:$i]:
% 38.48/38.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 38.48/38.69         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 38.48/38.69       ( ![C:$i]:
% 38.48/38.69         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 38.48/38.69           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 38.48/38.69  thf('12', plain,
% 38.48/38.69      (![X30 : $i, X31 : $i, X32 : $i]:
% 38.48/38.69         (~ (l1_pre_topc @ X30)
% 38.48/38.69          | ~ (v2_pre_topc @ X30)
% 38.48/38.69          | (v2_struct_0 @ X30)
% 38.48/38.69          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 38.48/38.69          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 38.48/38.69          | ~ (m1_connsp_2 @ X32 @ X30 @ X31))),
% 38.48/38.69      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 38.48/38.69  thf('13', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 38.48/38.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | (v2_struct_0 @ sk_A)
% 38.48/38.69          | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69          | ~ (l1_pre_topc @ sk_A))),
% 38.48/38.69      inference('sup-', [status(thm)], ['11', '12'])).
% 38.48/38.69  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('16', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 38.48/38.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | (v2_struct_0 @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['13', '14', '15'])).
% 38.48/38.69  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('18', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 38.48/38.69      inference('clc', [status(thm)], ['16', '17'])).
% 38.48/38.69  thf('19', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['10', '18'])).
% 38.48/38.69  thf(t6_connsp_2, axiom,
% 38.48/38.69    (![A:$i]:
% 38.48/38.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 38.48/38.69       ( ![B:$i]:
% 38.48/38.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.48/38.69           ( ![C:$i]:
% 38.48/38.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 38.48/38.69               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 38.48/38.69  thf('20', plain,
% 38.48/38.69      (![X33 : $i, X34 : $i, X35 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 38.48/38.69          | ~ (m1_connsp_2 @ X33 @ X34 @ X35)
% 38.48/38.69          | (r2_hidden @ X35 @ X33)
% 38.48/38.69          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 38.48/38.69          | ~ (l1_pre_topc @ X34)
% 38.48/38.69          | ~ (v2_pre_topc @ X34)
% 38.48/38.69          | (v2_struct_0 @ X34))),
% 38.48/38.69      inference('cnf', [status(esa)], [t6_connsp_2])).
% 38.48/38.69  thf('21', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v2_struct_0 @ sk_A)
% 38.48/38.69          | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69          | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 38.48/38.69          | (r2_hidden @ X0 @ sk_C)
% 38.48/38.69          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 38.48/38.69      inference('sup-', [status(thm)], ['19', '20'])).
% 38.48/38.69  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('24', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v2_struct_0 @ sk_A)
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 38.48/38.69          | (r2_hidden @ X0 @ sk_C)
% 38.48/38.69          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 38.48/38.69      inference('demod', [status(thm)], ['21', '22', '23'])).
% 38.48/38.69  thf('25', plain,
% 38.48/38.69      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 38.48/38.69        | (r2_hidden @ sk_B @ sk_C)
% 38.48/38.69        | (v2_struct_0 @ sk_A))),
% 38.48/38.69      inference('sup-', [status(thm)], ['1', '24'])).
% 38.48/38.69  thf('26', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 38.48/38.69      inference('clc', [status(thm)], ['8', '9'])).
% 38.48/38.69  thf('27', plain, (((r2_hidden @ sk_B @ sk_C) | (v2_struct_0 @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['25', '26'])).
% 38.48/38.69  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('29', plain, ((r2_hidden @ sk_B @ sk_C)),
% 38.48/38.69      inference('clc', [status(thm)], ['27', '28'])).
% 38.48/38.69  thf(d3_xboole_0, axiom,
% 38.48/38.69    (![A:$i,B:$i,C:$i]:
% 38.48/38.69     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 38.48/38.69       ( ![D:$i]:
% 38.48/38.69         ( ( r2_hidden @ D @ C ) <=>
% 38.48/38.69           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 38.48/38.69  thf('30', plain,
% 38.48/38.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.48/38.69         (~ (r2_hidden @ X0 @ X3)
% 38.48/38.69          | (r2_hidden @ X0 @ X2)
% 38.48/38.69          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 38.48/38.69      inference('cnf', [status(esa)], [d3_xboole_0])).
% 38.48/38.69  thf('31', plain,
% 38.48/38.69      (![X0 : $i, X1 : $i, X3 : $i]:
% 38.48/38.69         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 38.48/38.69      inference('simplify', [status(thm)], ['30'])).
% 38.48/38.69  thf('32', plain,
% 38.48/38.69      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 38.48/38.69      inference('sup-', [status(thm)], ['29', '31'])).
% 38.48/38.69  thf('33', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('34', plain,
% 38.48/38.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X40))
% 38.48/38.69          | (m1_connsp_2 @ X41 @ X40 @ X39)
% 38.48/38.69          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ (k9_yellow_6 @ X40 @ X39)))
% 38.48/38.69          | ~ (l1_pre_topc @ X40)
% 38.48/38.69          | ~ (v2_pre_topc @ X40)
% 38.48/38.69          | (v2_struct_0 @ X40))),
% 38.48/38.69      inference('cnf', [status(esa)], [t21_waybel_9])).
% 38.48/38.69  thf('35', plain,
% 38.48/38.69      (((v2_struct_0 @ sk_A)
% 38.48/38.69        | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69        | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69        | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['33', '34'])).
% 38.48/38.69  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('38', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('39', plain,
% 38.48/38.69      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 38.48/38.69      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 38.48/38.69  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('41', plain, ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)),
% 38.48/38.69      inference('clc', [status(thm)], ['39', '40'])).
% 38.48/38.69  thf('42', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 38.48/38.69      inference('clc', [status(thm)], ['16', '17'])).
% 38.48/38.69  thf('43', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['41', '42'])).
% 38.48/38.69  thf('44', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['10', '18'])).
% 38.48/38.69  thf(dt_k4_subset_1, axiom,
% 38.48/38.69    (![A:$i,B:$i,C:$i]:
% 38.48/38.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 38.48/38.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 38.48/38.69       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 38.48/38.69  thf('45', plain,
% 38.48/38.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 38.48/38.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 38.48/38.69          | (m1_subset_1 @ (k4_subset_1 @ X14 @ X13 @ X15) @ 
% 38.48/38.69             (k1_zfmisc_1 @ X14)))),
% 38.48/38.69      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 38.48/38.69  thf('46', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 38.48/38.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 38.48/38.69      inference('sup-', [status(thm)], ['44', '45'])).
% 38.48/38.69  thf('47', plain,
% 38.48/38.69      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 38.48/38.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['43', '46'])).
% 38.48/38.69  thf('48', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['41', '42'])).
% 38.48/38.69  thf('49', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['10', '18'])).
% 38.48/38.69  thf(redefinition_k4_subset_1, axiom,
% 38.48/38.69    (![A:$i,B:$i,C:$i]:
% 38.48/38.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 38.48/38.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 38.48/38.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 38.48/38.69  thf('50', plain,
% 38.48/38.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 38.48/38.69          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 38.48/38.69          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 38.48/38.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 38.48/38.69  thf('51', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 38.48/38.69            = (k2_xboole_0 @ sk_C @ X0))
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 38.48/38.69      inference('sup-', [status(thm)], ['49', '50'])).
% 38.48/38.69  thf('52', plain,
% 38.48/38.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 38.48/38.69         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 38.48/38.69      inference('sup-', [status(thm)], ['48', '51'])).
% 38.48/38.69  thf('53', plain,
% 38.48/38.69      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('demod', [status(thm)], ['47', '52'])).
% 38.48/38.69  thf(t39_yellow_6, axiom,
% 38.48/38.69    (![A:$i]:
% 38.48/38.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 38.48/38.69       ( ![B:$i]:
% 38.48/38.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 38.48/38.69           ( ![C:$i]:
% 38.48/38.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.48/38.69               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 38.48/38.69                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 38.48/38.69  thf('54', plain,
% 38.48/38.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 38.48/38.69          | ~ (r2_hidden @ X36 @ X38)
% 38.48/38.69          | ~ (v3_pre_topc @ X38 @ X37)
% 38.48/38.69          | (r2_hidden @ X38 @ (u1_struct_0 @ (k9_yellow_6 @ X37 @ X36)))
% 38.48/38.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 38.48/38.69          | ~ (l1_pre_topc @ X37)
% 38.48/38.69          | ~ (v2_pre_topc @ X37)
% 38.48/38.69          | (v2_struct_0 @ X37))),
% 38.48/38.69      inference('cnf', [status(esa)], [t39_yellow_6])).
% 38.48/38.69  thf('55', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v2_struct_0 @ sk_A)
% 38.48/38.69          | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69          | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 38.48/38.69          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 38.48/38.69          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['53', '54'])).
% 38.48/38.69  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('58', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v2_struct_0 @ sk_A)
% 38.48/38.69          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 38.48/38.69          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 38.48/38.69          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('demod', [status(thm)], ['55', '56', '57'])).
% 38.48/38.69  thf('59', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['41', '42'])).
% 38.48/38.69  thf('60', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['10', '18'])).
% 38.48/38.69  thf(fc7_tops_1, axiom,
% 38.48/38.69    (![A:$i,B:$i,C:$i]:
% 38.48/38.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 38.48/38.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 38.48/38.69         ( v3_pre_topc @ C @ A ) & 
% 38.48/38.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 38.48/38.69       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 38.48/38.69  thf('61', plain,
% 38.48/38.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 38.48/38.69          | ~ (v3_pre_topc @ X27 @ X28)
% 38.48/38.69          | ~ (l1_pre_topc @ X28)
% 38.48/38.69          | ~ (v2_pre_topc @ X28)
% 38.48/38.69          | ~ (v3_pre_topc @ X29 @ X28)
% 38.48/38.69          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 38.48/38.69          | (v3_pre_topc @ (k2_xboole_0 @ X27 @ X29) @ X28))),
% 38.48/38.69      inference('cnf', [status(esa)], [fc7_tops_1])).
% 38.48/38.69  thf('62', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | ~ (v3_pre_topc @ X0 @ sk_A)
% 38.48/38.69          | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69          | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 38.48/38.69      inference('sup-', [status(thm)], ['60', '61'])).
% 38.48/38.69  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('65', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | ~ (v3_pre_topc @ X0 @ sk_A)
% 38.48/38.69          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['62', '63', '64'])).
% 38.48/38.69  thf('66', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf(d2_subset_1, axiom,
% 38.48/38.69    (![A:$i,B:$i]:
% 38.48/38.69     ( ( ( v1_xboole_0 @ A ) =>
% 38.48/38.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 38.48/38.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 38.48/38.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 38.48/38.69  thf('67', plain,
% 38.48/38.69      (![X8 : $i, X9 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X8 @ X9)
% 38.48/38.69          | (r2_hidden @ X8 @ X9)
% 38.48/38.69          | (v1_xboole_0 @ X9))),
% 38.48/38.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 38.48/38.69  thf('68', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 38.48/38.69      inference('sup-', [status(thm)], ['66', '67'])).
% 38.48/38.69  thf('69', plain,
% 38.48/38.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 38.48/38.69          | ~ (r2_hidden @ X38 @ (u1_struct_0 @ (k9_yellow_6 @ X37 @ X36)))
% 38.48/38.69          | (v3_pre_topc @ X38 @ X37)
% 38.48/38.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 38.48/38.69          | ~ (l1_pre_topc @ X37)
% 38.48/38.69          | ~ (v2_pre_topc @ X37)
% 38.48/38.69          | (v2_struct_0 @ X37))),
% 38.48/38.69      inference('cnf', [status(esa)], [t39_yellow_6])).
% 38.48/38.69  thf('70', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A)
% 38.48/38.69        | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69        | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69        | (v3_pre_topc @ sk_C @ sk_A)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['68', '69'])).
% 38.48/38.69  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('74', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69        | (v3_pre_topc @ sk_C @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 38.48/38.69  thf('75', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['10', '18'])).
% 38.48/38.69  thf('76', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A)
% 38.48/38.69        | (v3_pre_topc @ sk_C @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['74', '75'])).
% 38.48/38.69  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('78', plain,
% 38.48/38.69      (((v3_pre_topc @ sk_C @ sk_A)
% 38.48/38.69        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 38.48/38.69      inference('clc', [status(thm)], ['76', '77'])).
% 38.48/38.69  thf('79', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('80', plain,
% 38.48/38.69      (![X9 : $i, X10 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X10 @ X9)
% 38.48/38.69          | (v1_xboole_0 @ X10)
% 38.48/38.69          | ~ (v1_xboole_0 @ X9))),
% 38.48/38.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 38.48/38.69  thf('81', plain,
% 38.48/38.69      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v1_xboole_0 @ sk_C))),
% 38.48/38.69      inference('sup-', [status(thm)], ['79', '80'])).
% 38.48/38.69  thf('82', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 38.48/38.69      inference('sup-', [status(thm)], ['78', '81'])).
% 38.48/38.69  thf('83', plain, ((r2_hidden @ sk_B @ sk_C)),
% 38.48/38.69      inference('clc', [status(thm)], ['27', '28'])).
% 38.48/38.69  thf(dt_k2_subset_1, axiom,
% 38.48/38.69    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 38.48/38.69  thf('84', plain,
% 38.48/38.69      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 38.48/38.69      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 38.48/38.69  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 38.48/38.69  thf('85', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 38.48/38.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 38.48/38.69  thf('86', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 38.48/38.69      inference('demod', [status(thm)], ['84', '85'])).
% 38.48/38.69  thf(t5_subset, axiom,
% 38.48/38.69    (![A:$i,B:$i,C:$i]:
% 38.48/38.69     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 38.48/38.69          ( v1_xboole_0 @ C ) ) ))).
% 38.48/38.69  thf('87', plain,
% 38.48/38.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 38.48/38.69         (~ (r2_hidden @ X24 @ X25)
% 38.48/38.69          | ~ (v1_xboole_0 @ X26)
% 38.48/38.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 38.48/38.69      inference('cnf', [status(esa)], [t5_subset])).
% 38.48/38.69  thf('88', plain,
% 38.48/38.69      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 38.48/38.69      inference('sup-', [status(thm)], ['86', '87'])).
% 38.48/38.69  thf('89', plain, (~ (v1_xboole_0 @ sk_C)),
% 38.48/38.69      inference('sup-', [status(thm)], ['83', '88'])).
% 38.48/38.69  thf('90', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 38.48/38.69      inference('clc', [status(thm)], ['82', '89'])).
% 38.48/38.69  thf('91', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['65', '90'])).
% 38.48/38.69  thf('92', plain,
% 38.48/38.69      ((~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 38.48/38.69        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A))),
% 38.48/38.69      inference('sup-', [status(thm)], ['59', '91'])).
% 38.48/38.69  thf('93', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('94', plain,
% 38.48/38.69      (![X8 : $i, X9 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X8 @ X9)
% 38.48/38.69          | (r2_hidden @ X8 @ X9)
% 38.48/38.69          | (v1_xboole_0 @ X9))),
% 38.48/38.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 38.48/38.69  thf('95', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 38.48/38.69      inference('sup-', [status(thm)], ['93', '94'])).
% 38.48/38.69  thf('96', plain,
% 38.48/38.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 38.48/38.69         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 38.48/38.69          | ~ (r2_hidden @ X38 @ (u1_struct_0 @ (k9_yellow_6 @ X37 @ X36)))
% 38.48/38.69          | (v3_pre_topc @ X38 @ X37)
% 38.48/38.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 38.48/38.69          | ~ (l1_pre_topc @ X37)
% 38.48/38.69          | ~ (v2_pre_topc @ X37)
% 38.48/38.69          | (v2_struct_0 @ X37))),
% 38.48/38.69      inference('cnf', [status(esa)], [t39_yellow_6])).
% 38.48/38.69  thf('97', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A)
% 38.48/38.69        | ~ (v2_pre_topc @ sk_A)
% 38.48/38.69        | ~ (l1_pre_topc @ sk_A)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69        | (v3_pre_topc @ sk_D_1 @ sk_A)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['95', '96'])).
% 38.48/38.69  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('100', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('101', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A)
% 38.48/38.69        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.48/38.69        | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 38.48/38.69  thf('102', plain,
% 38.48/38.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['41', '42'])).
% 38.48/38.69  thf('103', plain,
% 38.48/38.69      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A)
% 38.48/38.69        | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['101', '102'])).
% 38.48/38.69  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('105', plain,
% 38.48/38.69      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 38.48/38.69        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 38.48/38.69      inference('clc', [status(thm)], ['103', '104'])).
% 38.48/38.69  thf('106', plain,
% 38.48/38.69      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v1_xboole_0 @ sk_C))),
% 38.48/38.69      inference('sup-', [status(thm)], ['79', '80'])).
% 38.48/38.69  thf('107', plain, (((v3_pre_topc @ sk_D_1 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 38.48/38.69      inference('sup-', [status(thm)], ['105', '106'])).
% 38.48/38.69  thf('108', plain, (~ (v1_xboole_0 @ sk_C)),
% 38.48/38.69      inference('sup-', [status(thm)], ['83', '88'])).
% 38.48/38.69  thf('109', plain, ((v3_pre_topc @ sk_D_1 @ sk_A)),
% 38.48/38.69      inference('clc', [status(thm)], ['107', '108'])).
% 38.48/38.69  thf('110', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)),
% 38.48/38.69      inference('demod', [status(thm)], ['92', '109'])).
% 38.48/38.69  thf('111', plain,
% 38.48/38.69      (![X0 : $i]:
% 38.48/38.69         ((v2_struct_0 @ sk_A)
% 38.48/38.69          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 38.48/38.69          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 38.48/38.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 38.48/38.69      inference('demod', [status(thm)], ['58', '110'])).
% 38.48/38.69  thf('112', plain,
% 38.48/38.69      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 38.48/38.69        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A))),
% 38.48/38.69      inference('sup-', [status(thm)], ['32', '111'])).
% 38.48/38.69  thf('113', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('114', plain,
% 38.48/38.69      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 38.48/38.69        | (v2_struct_0 @ sk_A))),
% 38.48/38.69      inference('demod', [status(thm)], ['112', '113'])).
% 38.48/38.69  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 38.48/38.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.48/38.69  thf('116', plain,
% 38.48/38.69      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('clc', [status(thm)], ['114', '115'])).
% 38.48/38.69  thf(t1_subset, axiom,
% 38.48/38.69    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 38.48/38.69  thf('117', plain,
% 38.48/38.69      (![X19 : $i, X20 : $i]:
% 38.48/38.69         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 38.48/38.69      inference('cnf', [status(esa)], [t1_subset])).
% 38.48/38.69  thf('118', plain,
% 38.48/38.69      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 38.48/38.69        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 38.48/38.69      inference('sup-', [status(thm)], ['116', '117'])).
% 38.48/38.69  thf('119', plain, ($false), inference('demod', [status(thm)], ['0', '118'])).
% 38.48/38.69  
% 38.48/38.69  % SZS output end Refutation
% 38.48/38.69  
% 38.48/38.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
