%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y1BXjEWK3V

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:29 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 412 expanded)
%              Number of leaves         :   28 ( 134 expanded)
%              Depth                    :   21
%              Number of atoms          : 1111 (7345 expanded)
%              Number of equality atoms :   12 (  48 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ X21 @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( ( sk_D @ X23 @ X21 @ X22 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D @ sk_C @ sk_B @ sk_A )
      = sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','3','4','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['15','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ X0 ) )
      | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( m1_subset_1 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( ( sk_D @ X23 @ X21 @ X22 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
      = sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
      = sk_D_1 ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
    = sk_D_1 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( m1_subset_1 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('59',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

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

thf('64',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( r2_hidden @ X26 @ ( u1_struct_0 @ ( k9_yellow_6 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v3_pre_topc @ ( sk_D @ X23 @ X21 @ X22 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','85'])).

thf('87',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v3_pre_topc @ ( sk_D @ X23 @ X21 @ X22 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k9_yellow_6 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
    = sk_D_1 ),
    inference(clc,[status(thm)],['38','39'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v3_pre_topc @ sk_D_1 @ sk_A ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['87','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('105',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('110',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y1BXjEWK3V
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.50/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.71  % Solved by: fo/fo7.sh
% 1.50/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.71  % done 1582 iterations in 1.278s
% 1.50/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.71  % SZS output start Refutation
% 1.50/1.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.50/1.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.50/1.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.50/1.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.50/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.50/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.50/1.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.50/1.71  thf(sk_C_type, type, sk_C: $i).
% 1.50/1.71  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 1.50/1.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.50/1.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.50/1.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.50/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.50/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.71  thf(t23_waybel_9, conjecture,
% 1.50/1.71    (![A:$i]:
% 1.50/1.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.50/1.71       ( ![B:$i]:
% 1.50/1.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.50/1.71           ( ![C:$i]:
% 1.50/1.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.50/1.71               ( ![D:$i]:
% 1.50/1.71                 ( ( m1_subset_1 @
% 1.50/1.71                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.50/1.71                   ( m1_subset_1 @
% 1.50/1.71                     ( k2_xboole_0 @ C @ D ) @ 
% 1.50/1.71                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 1.50/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.71    (~( ![A:$i]:
% 1.50/1.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.50/1.71            ( l1_pre_topc @ A ) ) =>
% 1.50/1.71          ( ![B:$i]:
% 1.50/1.71            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.50/1.71              ( ![C:$i]:
% 1.50/1.71                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.50/1.71                  ( ![D:$i]:
% 1.50/1.71                    ( ( m1_subset_1 @
% 1.50/1.71                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.50/1.71                      ( m1_subset_1 @
% 1.50/1.71                        ( k2_xboole_0 @ C @ D ) @ 
% 1.50/1.71                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 1.50/1.71    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 1.50/1.71  thf('0', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf(t38_yellow_6, axiom,
% 1.50/1.71    (![A:$i]:
% 1.50/1.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.50/1.71       ( ![B:$i]:
% 1.50/1.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.50/1.71           ( ![C:$i]:
% 1.50/1.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 1.50/1.71               ( ?[D:$i]:
% 1.50/1.71                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 1.50/1.71                   ( ( D ) = ( C ) ) & 
% 1.50/1.71                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 1.50/1.71  thf('1', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | (r2_hidden @ X21 @ (sk_D @ X23 @ X21 @ X22))
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('2', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | (r2_hidden @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['0', '1'])).
% 1.50/1.71  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('5', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('6', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | ((sk_D @ X23 @ X21 @ X22) = (X23))
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('7', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | ((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['5', '6'])).
% 1.50/1.71  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('11', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 1.50/1.71      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.50/1.71  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('13', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 1.50/1.71      inference('clc', [status(thm)], ['11', '12'])).
% 1.50/1.71  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('15', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 1.50/1.71      inference('demod', [status(thm)], ['2', '3', '4', '13', '14'])).
% 1.50/1.71  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('17', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.50/1.71      inference('clc', [status(thm)], ['15', '16'])).
% 1.50/1.71  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.50/1.71      inference('clc', [status(thm)], ['15', '16'])).
% 1.50/1.71  thf(t7_xboole_1, axiom,
% 1.50/1.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.50/1.71  thf('19', plain,
% 1.50/1.71      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.50/1.71  thf(t3_subset, axiom,
% 1.50/1.71    (![A:$i,B:$i]:
% 1.50/1.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.50/1.71  thf('20', plain,
% 1.50/1.71      (![X9 : $i, X11 : $i]:
% 1.50/1.71         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 1.50/1.71      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.71  thf('21', plain,
% 1.50/1.71      (![X0 : $i, X1 : $i]:
% 1.50/1.71         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['19', '20'])).
% 1.50/1.71  thf(t4_subset, axiom,
% 1.50/1.71    (![A:$i,B:$i,C:$i]:
% 1.50/1.71     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.50/1.71       ( m1_subset_1 @ A @ C ) ))).
% 1.50/1.71  thf('22', plain,
% 1.50/1.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.50/1.71         (~ (r2_hidden @ X12 @ X13)
% 1.50/1.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.50/1.71          | (m1_subset_1 @ X12 @ X14))),
% 1.50/1.71      inference('cnf', [status(esa)], [t4_subset])).
% 1.50/1.71  thf('23', plain,
% 1.50/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.71         ((m1_subset_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.50/1.71          | ~ (r2_hidden @ X2 @ X1))),
% 1.50/1.71      inference('sup-', [status(thm)], ['21', '22'])).
% 1.50/1.71  thf('24', plain,
% 1.50/1.71      (![X0 : $i]: (m1_subset_1 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 1.50/1.71      inference('sup-', [status(thm)], ['18', '23'])).
% 1.50/1.71  thf(t2_subset, axiom,
% 1.50/1.71    (![A:$i,B:$i]:
% 1.50/1.71     ( ( m1_subset_1 @ A @ B ) =>
% 1.50/1.71       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.50/1.71  thf('25', plain,
% 1.50/1.71      (![X7 : $i, X8 : $i]:
% 1.50/1.71         ((r2_hidden @ X7 @ X8)
% 1.50/1.71          | (v1_xboole_0 @ X8)
% 1.50/1.71          | ~ (m1_subset_1 @ X7 @ X8))),
% 1.50/1.71      inference('cnf', [status(esa)], [t2_subset])).
% 1.50/1.71  thf('26', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ X0))
% 1.50/1.71          | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['24', '25'])).
% 1.50/1.71  thf('27', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('28', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | (m1_subset_1 @ (sk_D @ X23 @ X21 @ X22) @ 
% 1.50/1.71             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('29', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ 
% 1.50/1.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['27', '28'])).
% 1.50/1.71  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('32', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('33', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | ((sk_D @ X23 @ X21 @ X22) = (X23))
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('34', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | ((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['32', '33'])).
% 1.50/1.71  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('38', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1)))),
% 1.50/1.71      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.50/1.71  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('40', plain, (((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))),
% 1.50/1.71      inference('clc', [status(thm)], ['38', '39'])).
% 1.50/1.71  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('42', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.50/1.71      inference('demod', [status(thm)], ['29', '30', '31', '40', '41'])).
% 1.50/1.71  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('44', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('clc', [status(thm)], ['42', '43'])).
% 1.50/1.71  thf('45', plain,
% 1.50/1.71      (![X9 : $i, X10 : $i]:
% 1.50/1.71         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.50/1.71      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.71  thf('46', plain, ((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('sup-', [status(thm)], ['44', '45'])).
% 1.50/1.71  thf('47', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('48', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | (m1_subset_1 @ (sk_D @ X23 @ X21 @ X22) @ 
% 1.50/1.71             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('49', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 1.50/1.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['47', '48'])).
% 1.50/1.71  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('52', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 1.50/1.71      inference('clc', [status(thm)], ['11', '12'])).
% 1.50/1.71  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('54', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.50/1.71      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.50/1.71  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('56', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('clc', [status(thm)], ['54', '55'])).
% 1.50/1.71  thf('57', plain,
% 1.50/1.71      (![X9 : $i, X10 : $i]:
% 1.50/1.71         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.50/1.71      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.71  thf('58', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('sup-', [status(thm)], ['56', '57'])).
% 1.50/1.71  thf(t8_xboole_1, axiom,
% 1.50/1.71    (![A:$i,B:$i,C:$i]:
% 1.50/1.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.50/1.71       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.50/1.71  thf('59', plain,
% 1.50/1.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.50/1.71         (~ (r1_tarski @ X2 @ X3)
% 1.50/1.71          | ~ (r1_tarski @ X4 @ X3)
% 1.50/1.71          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 1.50/1.71      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.50/1.71  thf('60', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))
% 1.50/1.71          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['58', '59'])).
% 1.50/1.71  thf('61', plain,
% 1.50/1.71      ((r1_tarski @ (k2_xboole_0 @ sk_C @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('sup-', [status(thm)], ['46', '60'])).
% 1.50/1.71  thf('62', plain,
% 1.50/1.71      (![X9 : $i, X11 : $i]:
% 1.50/1.71         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 1.50/1.71      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.71  thf('63', plain,
% 1.50/1.71      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['61', '62'])).
% 1.50/1.71  thf(t39_yellow_6, axiom,
% 1.50/1.71    (![A:$i]:
% 1.50/1.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.50/1.71       ( ![B:$i]:
% 1.50/1.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.50/1.71           ( ![C:$i]:
% 1.50/1.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.71               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 1.50/1.71                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.50/1.71  thf('64', plain,
% 1.50/1.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 1.50/1.71          | ~ (r2_hidden @ X24 @ X26)
% 1.50/1.71          | ~ (v3_pre_topc @ X26 @ X25)
% 1.50/1.71          | (r2_hidden @ X26 @ (u1_struct_0 @ (k9_yellow_6 @ X25 @ X24)))
% 1.50/1.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.50/1.71          | ~ (l1_pre_topc @ X25)
% 1.50/1.71          | ~ (v2_pre_topc @ X25)
% 1.50/1.71          | (v2_struct_0 @ X25))),
% 1.50/1.71      inference('cnf', [status(esa)], [t39_yellow_6])).
% 1.50/1.71  thf('65', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v2_struct_0 @ sk_A)
% 1.50/1.71          | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71          | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 1.50/1.71          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 1.50/1.71          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 1.50/1.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['63', '64'])).
% 1.50/1.71  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('68', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v2_struct_0 @ sk_A)
% 1.50/1.71          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 1.50/1.71          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 1.50/1.71          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 1.50/1.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.50/1.71  thf('69', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('clc', [status(thm)], ['42', '43'])).
% 1.50/1.71  thf('70', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('clc', [status(thm)], ['54', '55'])).
% 1.50/1.71  thf(fc7_tops_1, axiom,
% 1.50/1.71    (![A:$i,B:$i,C:$i]:
% 1.50/1.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 1.50/1.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.50/1.71         ( v3_pre_topc @ C @ A ) & 
% 1.50/1.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.50/1.71       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 1.50/1.71  thf('71', plain,
% 1.50/1.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.50/1.71          | ~ (v3_pre_topc @ X18 @ X19)
% 1.50/1.71          | ~ (l1_pre_topc @ X19)
% 1.50/1.71          | ~ (v2_pre_topc @ X19)
% 1.50/1.71          | ~ (v3_pre_topc @ X20 @ X19)
% 1.50/1.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.50/1.71          | (v3_pre_topc @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 1.50/1.71      inference('cnf', [status(esa)], [fc7_tops_1])).
% 1.50/1.71  thf('72', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.50/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.71          | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.50/1.71          | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71          | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 1.50/1.71      inference('sup-', [status(thm)], ['70', '71'])).
% 1.50/1.71  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('75', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.50/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.71          | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.50/1.71          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 1.50/1.71      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.50/1.71  thf('76', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('77', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | (v3_pre_topc @ (sk_D @ X23 @ X21 @ X22) @ X22)
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('78', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['76', '77'])).
% 1.50/1.71  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('81', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 1.50/1.71      inference('clc', [status(thm)], ['11', '12'])).
% 1.50/1.71  thf('82', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('83', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 1.50/1.71      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 1.50/1.71  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('85', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 1.50/1.71      inference('clc', [status(thm)], ['83', '84'])).
% 1.50/1.71  thf('86', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.50/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.71          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 1.50/1.71      inference('demod', [status(thm)], ['75', '85'])).
% 1.50/1.71  thf('87', plain,
% 1.50/1.71      ((~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 1.50/1.71        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A))),
% 1.50/1.71      inference('sup-', [status(thm)], ['69', '86'])).
% 1.50/1.71  thf('88', plain,
% 1.50/1.71      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('89', plain,
% 1.50/1.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.71         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.50/1.71          | (v3_pre_topc @ (sk_D @ X23 @ X21 @ X22) @ X22)
% 1.50/1.71          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k9_yellow_6 @ X22 @ X21)))
% 1.50/1.71          | ~ (l1_pre_topc @ X22)
% 1.50/1.71          | ~ (v2_pre_topc @ X22)
% 1.50/1.71          | (v2_struct_0 @ X22))),
% 1.50/1.71      inference('cnf', [status(esa)], [t38_yellow_6])).
% 1.50/1.71  thf('90', plain,
% 1.50/1.71      (((v2_struct_0 @ sk_A)
% 1.50/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.50/1.71        | (v3_pre_topc @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A)
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['88', '89'])).
% 1.50/1.71  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('93', plain, (((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))),
% 1.50/1.71      inference('clc', [status(thm)], ['38', '39'])).
% 1.50/1.71  thf('94', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('95', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 1.50/1.71      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 1.50/1.71  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('97', plain, ((v3_pre_topc @ sk_D_1 @ sk_A)),
% 1.50/1.71      inference('clc', [status(thm)], ['95', '96'])).
% 1.50/1.71  thf('98', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)),
% 1.50/1.71      inference('demod', [status(thm)], ['87', '97'])).
% 1.50/1.71  thf('99', plain,
% 1.50/1.71      (![X0 : $i]:
% 1.50/1.71         ((v2_struct_0 @ sk_A)
% 1.50/1.71          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 1.50/1.71          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 1.50/1.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.71      inference('demod', [status(thm)], ['68', '98'])).
% 1.50/1.71  thf('100', plain,
% 1.50/1.71      (((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 1.50/1.71        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.50/1.71        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 1.50/1.71        | (v2_struct_0 @ sk_A))),
% 1.50/1.71      inference('sup-', [status(thm)], ['26', '99'])).
% 1.50/1.71  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('102', plain,
% 1.50/1.71      (((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 1.50/1.71        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 1.50/1.71        | (v2_struct_0 @ sk_A))),
% 1.50/1.71      inference('demod', [status(thm)], ['100', '101'])).
% 1.50/1.71  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('104', plain,
% 1.50/1.71      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 1.50/1.71        | (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 1.50/1.71      inference('clc', [status(thm)], ['102', '103'])).
% 1.50/1.71  thf(t1_subset, axiom,
% 1.50/1.71    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.50/1.71  thf('105', plain,
% 1.50/1.71      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.50/1.71      inference('cnf', [status(esa)], [t1_subset])).
% 1.50/1.71  thf('106', plain,
% 1.50/1.71      (((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 1.50/1.71        | (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 1.50/1.71      inference('sup-', [status(thm)], ['104', '105'])).
% 1.50/1.71  thf('107', plain,
% 1.50/1.71      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 1.50/1.71          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 1.50/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.71  thf('108', plain, ((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))),
% 1.50/1.71      inference('clc', [status(thm)], ['106', '107'])).
% 1.50/1.71  thf('109', plain,
% 1.50/1.71      (![X0 : $i, X1 : $i]:
% 1.50/1.71         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.71      inference('sup-', [status(thm)], ['19', '20'])).
% 1.50/1.71  thf(t5_subset, axiom,
% 1.50/1.71    (![A:$i,B:$i,C:$i]:
% 1.50/1.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.50/1.71          ( v1_xboole_0 @ C ) ) ))).
% 1.50/1.71  thf('110', plain,
% 1.50/1.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.50/1.71         (~ (r2_hidden @ X15 @ X16)
% 1.50/1.71          | ~ (v1_xboole_0 @ X17)
% 1.50/1.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.50/1.71      inference('cnf', [status(esa)], [t5_subset])).
% 1.50/1.71  thf('111', plain,
% 1.50/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.71         (~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 1.50/1.71      inference('sup-', [status(thm)], ['109', '110'])).
% 1.50/1.71  thf('112', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 1.50/1.71      inference('sup-', [status(thm)], ['108', '111'])).
% 1.50/1.71  thf('113', plain, ($false), inference('sup-', [status(thm)], ['17', '112'])).
% 1.50/1.71  
% 1.50/1.71  % SZS output end Refutation
% 1.50/1.71  
% 1.50/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
