%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T719bvQncq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:29 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 374 expanded)
%              Number of leaves         :   26 ( 121 expanded)
%              Depth                    :   19
%              Number of atoms          : 1163 (6668 expanded)
%              Number of equality atoms :   23 (  58 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r2_hidden @ X23 @ ( sk_D_2 @ X25 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( sk_D_2 @ X25 @ X23 @ X24 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
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
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
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
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( sk_D_2 @ X25 @ X23 @ X24 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
      = sk_D_3 )
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
    | ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
      = sk_D_3 ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
    = sk_D_3 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X28 )
      | ~ ( v3_pre_topc @ X28 @ X27 )
      | ( r2_hidden @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) )
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
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v3_pre_topc @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
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
    ( ~ ( v3_pre_topc @ sk_D_3 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v3_pre_topc @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
    = sk_D_3 ),
    inference(clc,[status(thm)],['33','34'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_3 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_pre_topc @ sk_D_3 @ sk_A ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A ),
    inference(demod,[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','93'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['101'])).

thf('103',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['101'])).

thf('107',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('108',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('109',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('112',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T719bvQncq
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:23:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.37/1.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.63  % Solved by: fo/fo7.sh
% 1.37/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.63  % done 1254 iterations in 1.183s
% 1.37/1.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.63  % SZS output start Refutation
% 1.37/1.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.37/1.63  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.37/1.63  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.37/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.37/1.63  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.37/1.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.37/1.63  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.63  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 1.37/1.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.37/1.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.37/1.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.37/1.63  thf(t23_waybel_9, conjecture,
% 1.37/1.63    (![A:$i]:
% 1.37/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.37/1.63       ( ![B:$i]:
% 1.37/1.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.37/1.63           ( ![C:$i]:
% 1.37/1.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.37/1.63               ( ![D:$i]:
% 1.37/1.63                 ( ( m1_subset_1 @
% 1.37/1.63                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.37/1.63                   ( m1_subset_1 @
% 1.37/1.63                     ( k2_xboole_0 @ C @ D ) @ 
% 1.37/1.63                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.63    (~( ![A:$i]:
% 1.37/1.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.37/1.63            ( l1_pre_topc @ A ) ) =>
% 1.37/1.63          ( ![B:$i]:
% 1.37/1.63            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.37/1.63              ( ![C:$i]:
% 1.37/1.63                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.37/1.63                  ( ![D:$i]:
% 1.37/1.63                    ( ( m1_subset_1 @
% 1.37/1.63                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.37/1.63                      ( m1_subset_1 @
% 1.37/1.63                        ( k2_xboole_0 @ C @ D ) @ 
% 1.37/1.63                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 1.37/1.63    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 1.37/1.63  thf('0', plain,
% 1.37/1.63      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.63          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('1', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf(t38_yellow_6, axiom,
% 1.37/1.63    (![A:$i]:
% 1.37/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.37/1.63       ( ![B:$i]:
% 1.37/1.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.37/1.63           ( ![C:$i]:
% 1.37/1.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.37/1.63               ( ?[D:$i]:
% 1.37/1.63                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 1.37/1.63                   ( ( D ) = ( C ) ) & 
% 1.37/1.63                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.63  thf('2', plain,
% 1.37/1.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.63          | (r2_hidden @ X23 @ (sk_D_2 @ X25 @ X23 @ X24))
% 1.37/1.63          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.63          | ~ (l1_pre_topc @ X24)
% 1.37/1.63          | ~ (v2_pre_topc @ X24)
% 1.37/1.63          | (v2_struct_0 @ X24))),
% 1.37/1.63      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.63  thf('3', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.63        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.63        | (r2_hidden @ sk_B @ (sk_D_2 @ sk_C @ sk_B @ sk_A))
% 1.37/1.63        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['1', '2'])).
% 1.37/1.63  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('6', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('7', plain,
% 1.37/1.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.63          | ((sk_D_2 @ X25 @ X23 @ X24) = (X25))
% 1.37/1.63          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.63          | ~ (l1_pre_topc @ X24)
% 1.37/1.63          | ~ (v2_pre_topc @ X24)
% 1.37/1.63          | (v2_struct_0 @ X24))),
% 1.37/1.63      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.63  thf('8', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.63        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.63        | ((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 1.37/1.63        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['6', '7'])).
% 1.37/1.63  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('12', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A) | ((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 1.37/1.63      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 1.37/1.63  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('14', plain, (((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 1.37/1.63      inference('clc', [status(thm)], ['12', '13'])).
% 1.37/1.63  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 1.37/1.63      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 1.37/1.63  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.37/1.63      inference('clc', [status(thm)], ['16', '17'])).
% 1.37/1.63  thf(d3_xboole_0, axiom,
% 1.37/1.63    (![A:$i,B:$i,C:$i]:
% 1.37/1.63     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.37/1.63       ( ![D:$i]:
% 1.37/1.63         ( ( r2_hidden @ D @ C ) <=>
% 1.37/1.63           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.37/1.63  thf('19', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.37/1.63         (~ (r2_hidden @ X0 @ X3)
% 1.37/1.63          | (r2_hidden @ X0 @ X2)
% 1.37/1.63          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.37/1.63      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.37/1.63  thf('20', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.37/1.63         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.37/1.63      inference('simplify', [status(thm)], ['19'])).
% 1.37/1.63  thf('21', plain,
% 1.37/1.63      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 1.37/1.63      inference('sup-', [status(thm)], ['18', '20'])).
% 1.37/1.63  thf('22', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('23', plain,
% 1.37/1.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.63          | (m1_subset_1 @ (sk_D_2 @ X25 @ X23 @ X24) @ 
% 1.37/1.63             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.37/1.63          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.63          | ~ (l1_pre_topc @ X24)
% 1.37/1.63          | ~ (v2_pre_topc @ X24)
% 1.37/1.63          | (v2_struct_0 @ X24))),
% 1.37/1.63      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.63  thf('24', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.63        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.63        | (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_A) @ 
% 1.37/1.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.37/1.63        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['22', '23'])).
% 1.37/1.63  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('27', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('28', plain,
% 1.37/1.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.63          | ((sk_D_2 @ X25 @ X23 @ X24) = (X25))
% 1.37/1.63          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.63          | ~ (l1_pre_topc @ X24)
% 1.37/1.63          | ~ (v2_pre_topc @ X24)
% 1.37/1.63          | (v2_struct_0 @ X24))),
% 1.37/1.63      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.63  thf('29', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.63        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.63        | ((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3))
% 1.37/1.63        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['27', '28'])).
% 1.37/1.63  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('33', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A) | ((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3)))),
% 1.37/1.63      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 1.37/1.63  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('35', plain, (((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3))),
% 1.37/1.63      inference('clc', [status(thm)], ['33', '34'])).
% 1.37/1.63  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('37', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | (m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.37/1.63      inference('demod', [status(thm)], ['24', '25', '26', '35', '36'])).
% 1.37/1.63  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('39', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('clc', [status(thm)], ['37', '38'])).
% 1.37/1.63  thf(t3_subset, axiom,
% 1.37/1.63    (![A:$i,B:$i]:
% 1.37/1.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.37/1.63  thf('40', plain,
% 1.37/1.63      (![X14 : $i, X15 : $i]:
% 1.37/1.63         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.37/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.63  thf('41', plain, ((r1_tarski @ sk_D_3 @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('sup-', [status(thm)], ['39', '40'])).
% 1.37/1.63  thf('42', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('43', plain,
% 1.37/1.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.63          | (m1_subset_1 @ (sk_D_2 @ X25 @ X23 @ X24) @ 
% 1.37/1.63             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.37/1.63          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.63          | ~ (l1_pre_topc @ X24)
% 1.37/1.63          | ~ (v2_pre_topc @ X24)
% 1.37/1.63          | (v2_struct_0 @ X24))),
% 1.37/1.63      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.63  thf('44', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.63        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.63        | (m1_subset_1 @ (sk_D_2 @ sk_C @ sk_B @ sk_A) @ 
% 1.37/1.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.37/1.63        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['42', '43'])).
% 1.37/1.63  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('47', plain, (((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 1.37/1.63      inference('clc', [status(thm)], ['12', '13'])).
% 1.37/1.63  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('49', plain,
% 1.37/1.63      (((v2_struct_0 @ sk_A)
% 1.37/1.63        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.37/1.63      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 1.37/1.63  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('51', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('clc', [status(thm)], ['49', '50'])).
% 1.37/1.63  thf('52', plain,
% 1.37/1.63      (![X14 : $i, X15 : $i]:
% 1.37/1.63         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.37/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.63  thf('53', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('sup-', [status(thm)], ['51', '52'])).
% 1.37/1.63  thf(t8_xboole_1, axiom,
% 1.37/1.63    (![A:$i,B:$i,C:$i]:
% 1.37/1.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.37/1.63       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.37/1.63  thf('54', plain,
% 1.37/1.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.63         (~ (r1_tarski @ X8 @ X9)
% 1.37/1.63          | ~ (r1_tarski @ X10 @ X9)
% 1.37/1.63          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.37/1.63      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.37/1.63  thf('55', plain,
% 1.37/1.63      (![X0 : $i]:
% 1.37/1.63         ((r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))
% 1.37/1.63          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.63  thf('56', plain,
% 1.37/1.63      ((r1_tarski @ (k2_xboole_0 @ sk_C @ sk_D_3) @ (u1_struct_0 @ sk_A))),
% 1.37/1.63      inference('sup-', [status(thm)], ['41', '55'])).
% 1.37/1.63  thf('57', plain,
% 1.37/1.63      (![X14 : $i, X16 : $i]:
% 1.37/1.63         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.37/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.63  thf('58', plain,
% 1.37/1.63      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['56', '57'])).
% 1.37/1.63  thf(t39_yellow_6, axiom,
% 1.37/1.63    (![A:$i]:
% 1.37/1.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.37/1.63       ( ![B:$i]:
% 1.37/1.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.37/1.63           ( ![C:$i]:
% 1.37/1.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.37/1.63               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 1.37/1.63                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.37/1.63  thf('59', plain,
% 1.37/1.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 1.37/1.63          | ~ (r2_hidden @ X26 @ X28)
% 1.37/1.63          | ~ (v3_pre_topc @ X28 @ X27)
% 1.37/1.63          | (r2_hidden @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 1.37/1.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.37/1.63          | ~ (l1_pre_topc @ X27)
% 1.37/1.63          | ~ (v2_pre_topc @ X27)
% 1.37/1.63          | (v2_struct_0 @ X27))),
% 1.37/1.63      inference('cnf', [status(esa)], [t39_yellow_6])).
% 1.37/1.63  thf('60', plain,
% 1.37/1.63      (![X0 : $i]:
% 1.37/1.63         ((v2_struct_0 @ sk_A)
% 1.37/1.63          | ~ (v2_pre_topc @ sk_A)
% 1.37/1.63          | ~ (l1_pre_topc @ sk_A)
% 1.37/1.63          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.63             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 1.37/1.63          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A)
% 1.37/1.63          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_3))
% 1.37/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['58', '59'])).
% 1.37/1.63  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('63', plain,
% 1.37/1.63      (![X0 : $i]:
% 1.37/1.63         ((v2_struct_0 @ sk_A)
% 1.37/1.63          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.63             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 1.37/1.63          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A)
% 1.37/1.63          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_3))
% 1.37/1.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.37/1.63  thf('64', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('clc', [status(thm)], ['37', '38'])).
% 1.37/1.63  thf('65', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.63      inference('clc', [status(thm)], ['49', '50'])).
% 1.37/1.63  thf(fc7_tops_1, axiom,
% 1.37/1.63    (![A:$i,B:$i,C:$i]:
% 1.37/1.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 1.37/1.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.37/1.63         ( v3_pre_topc @ C @ A ) & 
% 1.37/1.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.37/1.63       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 1.37/1.63  thf('66', plain,
% 1.37/1.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.37/1.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.37/1.63          | ~ (v3_pre_topc @ X20 @ X21)
% 1.37/1.63          | ~ (l1_pre_topc @ X21)
% 1.37/1.63          | ~ (v2_pre_topc @ X21)
% 1.37/1.63          | ~ (v3_pre_topc @ X22 @ X21)
% 1.37/1.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.37/1.63          | (v3_pre_topc @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 1.37/1.63      inference('cnf', [status(esa)], [fc7_tops_1])).
% 1.37/1.64  thf('67', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.37/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.37/1.64          | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.37/1.64          | ~ (v2_pre_topc @ sk_A)
% 1.37/1.64          | ~ (l1_pre_topc @ sk_A)
% 1.37/1.64          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 1.37/1.64      inference('sup-', [status(thm)], ['65', '66'])).
% 1.37/1.64  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('70', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.37/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.37/1.64          | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.37/1.64          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 1.37/1.64      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.37/1.64  thf('71', plain,
% 1.37/1.64      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('72', plain,
% 1.37/1.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.64         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.64          | (v3_pre_topc @ (sk_D_2 @ X25 @ X23 @ X24) @ X24)
% 1.37/1.64          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.64          | ~ (l1_pre_topc @ X24)
% 1.37/1.64          | ~ (v2_pre_topc @ X24)
% 1.37/1.64          | (v2_struct_0 @ X24))),
% 1.37/1.64      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.64  thf('73', plain,
% 1.37/1.64      (((v2_struct_0 @ sk_A)
% 1.37/1.64        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.64        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.64        | (v3_pre_topc @ (sk_D_2 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 1.37/1.64        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.64      inference('sup-', [status(thm)], ['71', '72'])).
% 1.37/1.64  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('76', plain, (((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 1.37/1.64      inference('clc', [status(thm)], ['12', '13'])).
% 1.37/1.64  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('78', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 1.37/1.64      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.37/1.64  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('80', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 1.37/1.64      inference('clc', [status(thm)], ['78', '79'])).
% 1.37/1.64  thf('81', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.37/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.37/1.64          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 1.37/1.64      inference('demod', [status(thm)], ['70', '80'])).
% 1.37/1.64  thf('82', plain,
% 1.37/1.64      ((~ (v3_pre_topc @ sk_D_3 @ sk_A)
% 1.37/1.64        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A))),
% 1.37/1.64      inference('sup-', [status(thm)], ['64', '81'])).
% 1.37/1.64  thf('83', plain,
% 1.37/1.64      ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('84', plain,
% 1.37/1.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.64         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 1.37/1.64          | (v3_pre_topc @ (sk_D_2 @ X25 @ X23 @ X24) @ X24)
% 1.37/1.64          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 1.37/1.64          | ~ (l1_pre_topc @ X24)
% 1.37/1.64          | ~ (v2_pre_topc @ X24)
% 1.37/1.64          | (v2_struct_0 @ X24))),
% 1.37/1.64      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.37/1.64  thf('85', plain,
% 1.37/1.64      (((v2_struct_0 @ sk_A)
% 1.37/1.64        | ~ (v2_pre_topc @ sk_A)
% 1.37/1.64        | ~ (l1_pre_topc @ sk_A)
% 1.37/1.64        | (v3_pre_topc @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 1.37/1.64        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.37/1.64      inference('sup-', [status(thm)], ['83', '84'])).
% 1.37/1.64  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('88', plain, (((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3))),
% 1.37/1.64      inference('clc', [status(thm)], ['33', '34'])).
% 1.37/1.64  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('90', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_3 @ sk_A))),
% 1.37/1.64      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 1.37/1.64  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('92', plain, ((v3_pre_topc @ sk_D_3 @ sk_A)),
% 1.37/1.64      inference('clc', [status(thm)], ['90', '91'])).
% 1.37/1.64  thf('93', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A)),
% 1.37/1.64      inference('demod', [status(thm)], ['82', '92'])).
% 1.37/1.64  thf('94', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         ((v2_struct_0 @ sk_A)
% 1.37/1.64          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.64             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 1.37/1.64          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_3))
% 1.37/1.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.37/1.64      inference('demod', [status(thm)], ['63', '93'])).
% 1.37/1.64  thf('95', plain,
% 1.37/1.64      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.37/1.64        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.64           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 1.37/1.64        | (v2_struct_0 @ sk_A))),
% 1.37/1.64      inference('sup-', [status(thm)], ['21', '94'])).
% 1.37/1.64  thf('96', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('97', plain,
% 1.37/1.64      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.64         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 1.37/1.64        | (v2_struct_0 @ sk_A))),
% 1.37/1.64      inference('demod', [status(thm)], ['95', '96'])).
% 1.37/1.64  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 1.37/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.64  thf('99', plain,
% 1.37/1.64      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.64        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.64      inference('clc', [status(thm)], ['97', '98'])).
% 1.37/1.64  thf('100', plain,
% 1.37/1.64      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.37/1.64         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.37/1.64          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.37/1.64          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 1.37/1.64          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.37/1.64      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.37/1.64  thf('101', plain,
% 1.37/1.64      (![X0 : $i, X1 : $i]:
% 1.37/1.64         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.37/1.64          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 1.37/1.64          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 1.37/1.64      inference('eq_fact', [status(thm)], ['100'])).
% 1.37/1.64  thf('102', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.37/1.64          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.37/1.64      inference('eq_fact', [status(thm)], ['101'])).
% 1.37/1.64  thf('103', plain,
% 1.37/1.64      (![X1 : $i, X3 : $i, X5 : $i]:
% 1.37/1.64         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 1.37/1.64          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 1.37/1.64          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 1.37/1.64      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.37/1.64  thf('104', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.37/1.64          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.37/1.64          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 1.37/1.64      inference('sup-', [status(thm)], ['102', '103'])).
% 1.37/1.64  thf('105', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.37/1.64          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 1.37/1.64      inference('simplify', [status(thm)], ['104'])).
% 1.37/1.64  thf('106', plain,
% 1.37/1.64      (![X0 : $i]:
% 1.37/1.64         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.37/1.64          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.37/1.64      inference('eq_fact', [status(thm)], ['101'])).
% 1.37/1.64  thf('107', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.37/1.64      inference('clc', [status(thm)], ['105', '106'])).
% 1.37/1.64  thf(t7_xboole_1, axiom,
% 1.37/1.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.37/1.64  thf('108', plain,
% 1.37/1.64      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.37/1.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.37/1.64  thf('109', plain,
% 1.37/1.64      (![X14 : $i, X16 : $i]:
% 1.37/1.64         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.37/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.64  thf('110', plain,
% 1.37/1.64      (![X0 : $i, X1 : $i]:
% 1.37/1.64         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.37/1.64      inference('sup-', [status(thm)], ['108', '109'])).
% 1.37/1.64  thf('111', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.37/1.64      inference('sup+', [status(thm)], ['107', '110'])).
% 1.37/1.64  thf(t4_subset, axiom,
% 1.37/1.64    (![A:$i,B:$i,C:$i]:
% 1.37/1.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.37/1.64       ( m1_subset_1 @ A @ C ) ))).
% 1.37/1.64  thf('112', plain,
% 1.37/1.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.37/1.64         (~ (r2_hidden @ X17 @ X18)
% 1.37/1.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.37/1.64          | (m1_subset_1 @ X17 @ X19))),
% 1.37/1.64      inference('cnf', [status(esa)], [t4_subset])).
% 1.37/1.64  thf('113', plain,
% 1.37/1.64      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.37/1.64      inference('sup-', [status(thm)], ['111', '112'])).
% 1.37/1.64  thf('114', plain,
% 1.37/1.64      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 1.37/1.64        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.37/1.64      inference('sup-', [status(thm)], ['99', '113'])).
% 1.37/1.64  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 1.37/1.64  
% 1.37/1.64  % SZS output end Refutation
% 1.37/1.64  
% 1.47/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
