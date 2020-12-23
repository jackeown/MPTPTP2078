%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VudSP5A4Ak

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:28 EST 2020

% Result     : Theorem 19.11s
% Output     : Refutation 19.11s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 429 expanded)
%              Number of leaves         :   24 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          : 1055 (8043 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ? [D: $i] :
                  ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ B @ D )
                  & ( D = C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X20 @ ( sk_D_1 @ X22 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( sk_D_1 @ X22 @ X20 @ X21 )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4','5','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['16','17'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( sk_D_1 @ X22 @ X20 @ X21 )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
      = sk_D_2 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
      = sk_D_2 ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_2 )
    = ( k2_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','57'])).

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

thf('59',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( r2_hidden @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','80'])).

thf('82',plain,
    ( ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['33','34'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_pre_topc @ sk_D_2 @ sk_A ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','93'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('100',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('101',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VudSP5A4Ak
% 0.13/0.36  % Computer   : n013.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:11:40 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 19.11/19.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.11/19.30  % Solved by: fo/fo7.sh
% 19.11/19.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.11/19.30  % done 13264 iterations in 18.864s
% 19.11/19.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.11/19.30  % SZS output start Refutation
% 19.11/19.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.11/19.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.11/19.30  thf(sk_C_type, type, sk_C: $i).
% 19.11/19.30  thf(sk_A_type, type, sk_A: $i).
% 19.11/19.30  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 19.11/19.30  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 19.11/19.30  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 19.11/19.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.11/19.30  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 19.11/19.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.11/19.30  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 19.11/19.30  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 19.11/19.30  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 19.11/19.30  thf(sk_B_type, type, sk_B: $i).
% 19.11/19.30  thf(sk_D_2_type, type, sk_D_2: $i).
% 19.11/19.30  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 19.11/19.30  thf(t23_waybel_9, conjecture,
% 19.11/19.30    (![A:$i]:
% 19.11/19.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.11/19.30       ( ![B:$i]:
% 19.11/19.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 19.11/19.30           ( ![C:$i]:
% 19.11/19.30             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 19.11/19.30               ( ![D:$i]:
% 19.11/19.30                 ( ( m1_subset_1 @
% 19.11/19.30                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 19.11/19.30                   ( m1_subset_1 @
% 19.11/19.30                     ( k2_xboole_0 @ C @ D ) @ 
% 19.11/19.30                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 19.11/19.30  thf(zf_stmt_0, negated_conjecture,
% 19.11/19.30    (~( ![A:$i]:
% 19.11/19.30        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 19.11/19.30            ( l1_pre_topc @ A ) ) =>
% 19.11/19.30          ( ![B:$i]:
% 19.11/19.30            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 19.11/19.30              ( ![C:$i]:
% 19.11/19.30                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 19.11/19.30                  ( ![D:$i]:
% 19.11/19.30                    ( ( m1_subset_1 @
% 19.11/19.30                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 19.11/19.30                      ( m1_subset_1 @
% 19.11/19.30                        ( k2_xboole_0 @ C @ D ) @ 
% 19.11/19.30                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 19.11/19.30    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 19.11/19.30  thf('0', plain,
% 19.11/19.30      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('1', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf(t38_yellow_6, axiom,
% 19.11/19.30    (![A:$i]:
% 19.11/19.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.11/19.30       ( ![B:$i]:
% 19.11/19.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 19.11/19.30           ( ![C:$i]:
% 19.11/19.30             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 19.11/19.30               ( ?[D:$i]:
% 19.11/19.30                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 19.11/19.30                   ( ( D ) = ( C ) ) & 
% 19.11/19.30                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 19.11/19.30  thf('2', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | (r2_hidden @ X20 @ (sk_D_1 @ X22 @ X20 @ X21))
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('3', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['1', '2'])).
% 19.11/19.30  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('6', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('7', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | ((sk_D_1 @ X22 @ X20 @ X21) = (X22))
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('8', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['6', '7'])).
% 19.11/19.30  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('12', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 19.11/19.30      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 19.11/19.30  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('14', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 19.11/19.30      inference('clc', [status(thm)], ['12', '13'])).
% 19.11/19.30  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 19.11/19.30      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 19.11/19.30  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 19.11/19.30      inference('clc', [status(thm)], ['16', '17'])).
% 19.11/19.30  thf(d3_xboole_0, axiom,
% 19.11/19.30    (![A:$i,B:$i,C:$i]:
% 19.11/19.30     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 19.11/19.30       ( ![D:$i]:
% 19.11/19.30         ( ( r2_hidden @ D @ C ) <=>
% 19.11/19.30           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 19.11/19.30  thf('19', plain,
% 19.11/19.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.11/19.30         (~ (r2_hidden @ X0 @ X3)
% 19.11/19.30          | (r2_hidden @ X0 @ X2)
% 19.11/19.30          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 19.11/19.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 19.11/19.30  thf('20', plain,
% 19.11/19.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 19.11/19.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 19.11/19.30      inference('simplify', [status(thm)], ['19'])).
% 19.11/19.30  thf('21', plain,
% 19.11/19.30      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 19.11/19.30      inference('sup-', [status(thm)], ['18', '20'])).
% 19.11/19.30  thf('22', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('23', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | (m1_subset_1 @ (sk_D_1 @ X22 @ X20 @ X21) @ 
% 19.11/19.30             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('24', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ 
% 19.11/19.30           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['22', '23'])).
% 19.11/19.30  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('27', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('28', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | ((sk_D_1 @ X22 @ X20 @ X21) = (X22))
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('29', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['27', '28'])).
% 19.11/19.30  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('33', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2)))),
% 19.11/19.30      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 19.11/19.30  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('35', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 19.11/19.30      inference('clc', [status(thm)], ['33', '34'])).
% 19.11/19.30  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('37', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.11/19.30      inference('demod', [status(thm)], ['24', '25', '26', '35', '36'])).
% 19.11/19.30  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('39', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('clc', [status(thm)], ['37', '38'])).
% 19.11/19.30  thf('40', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('41', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | (m1_subset_1 @ (sk_D_1 @ X22 @ X20 @ X21) @ 
% 19.11/19.30             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('42', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 19.11/19.30           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['40', '41'])).
% 19.11/19.30  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('45', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 19.11/19.30      inference('clc', [status(thm)], ['12', '13'])).
% 19.11/19.30  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('47', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.11/19.30      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 19.11/19.30  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('49', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('clc', [status(thm)], ['47', '48'])).
% 19.11/19.30  thf(dt_k4_subset_1, axiom,
% 19.11/19.30    (![A:$i,B:$i,C:$i]:
% 19.11/19.30     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 19.11/19.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 19.11/19.30       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 19.11/19.30  thf('50', plain,
% 19.11/19.30      (![X6 : $i, X7 : $i, X8 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 19.11/19.30          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 19.11/19.30          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 19.11/19.30      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 19.11/19.30  thf('51', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 19.11/19.30           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.11/19.30      inference('sup-', [status(thm)], ['49', '50'])).
% 19.11/19.30  thf('52', plain,
% 19.11/19.30      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_2) @ 
% 19.11/19.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['39', '51'])).
% 19.11/19.30  thf('53', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('clc', [status(thm)], ['37', '38'])).
% 19.11/19.30  thf('54', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('clc', [status(thm)], ['47', '48'])).
% 19.11/19.30  thf(redefinition_k4_subset_1, axiom,
% 19.11/19.30    (![A:$i,B:$i,C:$i]:
% 19.11/19.30     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 19.11/19.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 19.11/19.30       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 19.11/19.30  thf('55', plain,
% 19.11/19.30      (![X9 : $i, X10 : $i, X11 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 19.11/19.30          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 19.11/19.30          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 19.11/19.30      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 19.11/19.30  thf('56', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 19.11/19.30            = (k2_xboole_0 @ sk_C @ X0))
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.11/19.30      inference('sup-', [status(thm)], ['54', '55'])).
% 19.11/19.30  thf('57', plain,
% 19.11/19.30      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_2)
% 19.11/19.30         = (k2_xboole_0 @ sk_C @ sk_D_2))),
% 19.11/19.30      inference('sup-', [status(thm)], ['53', '56'])).
% 19.11/19.30  thf('58', plain,
% 19.11/19.30      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('demod', [status(thm)], ['52', '57'])).
% 19.11/19.30  thf(t39_yellow_6, axiom,
% 19.11/19.30    (![A:$i]:
% 19.11/19.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.11/19.30       ( ![B:$i]:
% 19.11/19.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 19.11/19.30           ( ![C:$i]:
% 19.11/19.30             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.11/19.30               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 19.11/19.30                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 19.11/19.30  thf('59', plain,
% 19.11/19.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 19.11/19.30          | ~ (r2_hidden @ X23 @ X25)
% 19.11/19.30          | ~ (v3_pre_topc @ X25 @ X24)
% 19.11/19.30          | (r2_hidden @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 19.11/19.30          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 19.11/19.30          | ~ (l1_pre_topc @ X24)
% 19.11/19.30          | ~ (v2_pre_topc @ X24)
% 19.11/19.30          | (v2_struct_0 @ X24))),
% 19.11/19.30      inference('cnf', [status(esa)], [t39_yellow_6])).
% 19.11/19.30  thf('60', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((v2_struct_0 @ sk_A)
% 19.11/19.30          | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30          | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 19.11/19.30          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_2) @ sk_A)
% 19.11/19.30          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_2))
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['58', '59'])).
% 19.11/19.30  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('63', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((v2_struct_0 @ sk_A)
% 19.11/19.30          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 19.11/19.30          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_2) @ sk_A)
% 19.11/19.30          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_2))
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('demod', [status(thm)], ['60', '61', '62'])).
% 19.11/19.30  thf('64', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('clc', [status(thm)], ['37', '38'])).
% 19.11/19.30  thf('65', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('clc', [status(thm)], ['47', '48'])).
% 19.11/19.30  thf(fc7_tops_1, axiom,
% 19.11/19.30    (![A:$i,B:$i,C:$i]:
% 19.11/19.30     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 19.11/19.30         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 19.11/19.30         ( v3_pre_topc @ C @ A ) & 
% 19.11/19.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 19.11/19.30       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 19.11/19.30  thf('66', plain,
% 19.11/19.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 19.11/19.30          | ~ (v3_pre_topc @ X17 @ X18)
% 19.11/19.30          | ~ (l1_pre_topc @ X18)
% 19.11/19.30          | ~ (v2_pre_topc @ X18)
% 19.11/19.30          | ~ (v3_pre_topc @ X19 @ X18)
% 19.11/19.30          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 19.11/19.30          | (v3_pre_topc @ (k2_xboole_0 @ X17 @ X19) @ X18))),
% 19.11/19.30      inference('cnf', [status(esa)], [fc7_tops_1])).
% 19.11/19.30  thf('67', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.11/19.30          | ~ (v3_pre_topc @ X0 @ sk_A)
% 19.11/19.30          | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30          | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 19.11/19.30      inference('sup-', [status(thm)], ['65', '66'])).
% 19.11/19.30  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('70', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.11/19.30          | ~ (v3_pre_topc @ X0 @ sk_A)
% 19.11/19.30          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 19.11/19.30      inference('demod', [status(thm)], ['67', '68', '69'])).
% 19.11/19.30  thf('71', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('72', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | (v3_pre_topc @ (sk_D_1 @ X22 @ X20 @ X21) @ X21)
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('73', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | (v3_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['71', '72'])).
% 19.11/19.30  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('76', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 19.11/19.30      inference('clc', [status(thm)], ['12', '13'])).
% 19.11/19.30  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('78', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 19.11/19.30      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 19.11/19.30  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('80', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 19.11/19.30      inference('clc', [status(thm)], ['78', '79'])).
% 19.11/19.30  thf('81', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.11/19.30          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 19.11/19.30      inference('demod', [status(thm)], ['70', '80'])).
% 19.11/19.30  thf('82', plain,
% 19.11/19.30      ((~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 19.11/19.30        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_2) @ sk_A))),
% 19.11/19.30      inference('sup-', [status(thm)], ['64', '81'])).
% 19.11/19.30  thf('83', plain,
% 19.11/19.30      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('84', plain,
% 19.11/19.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.11/19.30         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 19.11/19.30          | (v3_pre_topc @ (sk_D_1 @ X22 @ X20 @ X21) @ X21)
% 19.11/19.30          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 19.11/19.30          | ~ (l1_pre_topc @ X21)
% 19.11/19.30          | ~ (v2_pre_topc @ X21)
% 19.11/19.30          | (v2_struct_0 @ X21))),
% 19.11/19.30      inference('cnf', [status(esa)], [t38_yellow_6])).
% 19.11/19.30  thf('85', plain,
% 19.11/19.30      (((v2_struct_0 @ sk_A)
% 19.11/19.30        | ~ (v2_pre_topc @ sk_A)
% 19.11/19.30        | ~ (l1_pre_topc @ sk_A)
% 19.11/19.30        | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_A)
% 19.11/19.30        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['83', '84'])).
% 19.11/19.30  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('88', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 19.11/19.30      inference('clc', [status(thm)], ['33', '34'])).
% 19.11/19.30  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('90', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_2 @ sk_A))),
% 19.11/19.30      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 19.11/19.30  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('92', plain, ((v3_pre_topc @ sk_D_2 @ sk_A)),
% 19.11/19.30      inference('clc', [status(thm)], ['90', '91'])).
% 19.11/19.30  thf('93', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_2) @ sk_A)),
% 19.11/19.30      inference('demod', [status(thm)], ['82', '92'])).
% 19.11/19.30  thf('94', plain,
% 19.11/19.30      (![X0 : $i]:
% 19.11/19.30         ((v2_struct_0 @ sk_A)
% 19.11/19.30          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 19.11/19.30          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_2))
% 19.11/19.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 19.11/19.30      inference('demod', [status(thm)], ['63', '93'])).
% 19.11/19.30  thf('95', plain,
% 19.11/19.30      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 19.11/19.30        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 19.11/19.30        | (v2_struct_0 @ sk_A))),
% 19.11/19.30      inference('sup-', [status(thm)], ['21', '94'])).
% 19.11/19.30  thf('96', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('97', plain,
% 19.11/19.30      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 19.11/19.30        | (v2_struct_0 @ sk_A))),
% 19.11/19.30      inference('demod', [status(thm)], ['95', '96'])).
% 19.11/19.30  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 19.11/19.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.11/19.30  thf('99', plain,
% 19.11/19.30      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('clc', [status(thm)], ['97', '98'])).
% 19.11/19.30  thf(t1_subset, axiom,
% 19.11/19.30    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 19.11/19.30  thf('100', plain,
% 19.11/19.30      (![X12 : $i, X13 : $i]:
% 19.11/19.30         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 19.11/19.30      inference('cnf', [status(esa)], [t1_subset])).
% 19.11/19.30  thf('101', plain,
% 19.11/19.30      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 19.11/19.30        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 19.11/19.30      inference('sup-', [status(thm)], ['99', '100'])).
% 19.11/19.30  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 19.11/19.30  
% 19.11/19.30  % SZS output end Refutation
% 19.11/19.30  
% 19.11/19.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
