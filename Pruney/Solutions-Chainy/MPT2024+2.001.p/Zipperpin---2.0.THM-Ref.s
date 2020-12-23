%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TRvJCx8YZB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:26 EST 2020

% Result     : Theorem 29.44s
% Output     : Refutation 29.44s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 417 expanded)
%              Number of leaves         :   30 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          : 1128 (7362 expanded)
%              Number of equality atoms :   17 (  53 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_hidden @ X25 @ ( sk_D @ X27 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( ( sk_D @ X27 @ X25 @ X26 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( m1_subset_1 @ ( sk_D @ X27 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( ( sk_D @ X27 @ X25 @ X26 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( m1_subset_1 @ ( sk_D @ X27 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['49','63'])).

thf('65',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','64'])).

thf('66',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

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

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( r2_hidden @ X30 @ ( u1_struct_0 @ ( k9_yellow_6 @ X29 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( v3_pre_topc @ ( sk_D @ X27 @ X25 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_D @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('90',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( v3_pre_topc @ ( sk_D @ X27 @ X25 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
    = sk_D_1 ),
    inference(clc,[status(thm)],['38','39'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_pre_topc @ sk_D_1 @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['90','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('113',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TRvJCx8YZB
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:11 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 29.44/29.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.44/29.70  % Solved by: fo/fo7.sh
% 29.44/29.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.44/29.70  % done 37246 iterations in 29.248s
% 29.44/29.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.44/29.70  % SZS output start Refutation
% 29.44/29.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.44/29.70  thf(sk_B_type, type, sk_B: $i).
% 29.44/29.70  thf(sk_C_type, type, sk_C: $i).
% 29.44/29.70  thf(sk_A_type, type, sk_A: $i).
% 29.44/29.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 29.44/29.70  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 29.44/29.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 29.44/29.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 29.44/29.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 29.44/29.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 29.44/29.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.44/29.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.44/29.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 29.44/29.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 29.44/29.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 29.44/29.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.44/29.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 29.44/29.70  thf(t23_waybel_9, conjecture,
% 29.44/29.70    (![A:$i]:
% 29.44/29.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.44/29.70       ( ![B:$i]:
% 29.44/29.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.44/29.70           ( ![C:$i]:
% 29.44/29.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 29.44/29.70               ( ![D:$i]:
% 29.44/29.70                 ( ( m1_subset_1 @
% 29.44/29.70                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 29.44/29.70                   ( m1_subset_1 @
% 29.44/29.70                     ( k2_xboole_0 @ C @ D ) @ 
% 29.44/29.70                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 29.44/29.70  thf(zf_stmt_0, negated_conjecture,
% 29.44/29.70    (~( ![A:$i]:
% 29.44/29.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 29.44/29.70            ( l1_pre_topc @ A ) ) =>
% 29.44/29.70          ( ![B:$i]:
% 29.44/29.70            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.44/29.70              ( ![C:$i]:
% 29.44/29.70                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 29.44/29.70                  ( ![D:$i]:
% 29.44/29.70                    ( ( m1_subset_1 @
% 29.44/29.70                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 29.44/29.70                      ( m1_subset_1 @
% 29.44/29.70                        ( k2_xboole_0 @ C @ D ) @ 
% 29.44/29.70                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 29.44/29.70    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 29.44/29.70  thf('0', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf(t38_yellow_6, axiom,
% 29.44/29.70    (![A:$i]:
% 29.44/29.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.44/29.70       ( ![B:$i]:
% 29.44/29.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.44/29.70           ( ![C:$i]:
% 29.44/29.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 29.44/29.70               ( ?[D:$i]:
% 29.44/29.70                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 29.44/29.70                   ( ( D ) = ( C ) ) & 
% 29.44/29.70                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 29.44/29.70  thf('1', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | (r2_hidden @ X25 @ (sk_D @ X27 @ X25 @ X26))
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('2', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | (r2_hidden @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['0', '1'])).
% 29.44/29.70  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('5', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('6', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | ((sk_D @ X27 @ X25 @ X26) = (X27))
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('7', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | ((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['5', '6'])).
% 29.44/29.70  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('11', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 29.44/29.70      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 29.44/29.70  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('13', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 29.44/29.70      inference('clc', [status(thm)], ['11', '12'])).
% 29.44/29.70  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('15', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 29.44/29.70      inference('demod', [status(thm)], ['2', '3', '4', '13', '14'])).
% 29.44/29.70  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('17', plain, ((r2_hidden @ sk_B @ sk_C)),
% 29.44/29.70      inference('clc', [status(thm)], ['15', '16'])).
% 29.44/29.70  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 29.44/29.70      inference('clc', [status(thm)], ['15', '16'])).
% 29.44/29.70  thf(t7_xboole_1, axiom,
% 29.44/29.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 29.44/29.70  thf('19', plain,
% 29.44/29.70      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 29.44/29.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.44/29.70  thf(t3_subset, axiom,
% 29.44/29.70    (![A:$i,B:$i]:
% 29.44/29.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 29.44/29.70  thf('20', plain,
% 29.44/29.70      (![X13 : $i, X15 : $i]:
% 29.44/29.70         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 29.44/29.70      inference('cnf', [status(esa)], [t3_subset])).
% 29.44/29.70  thf('21', plain,
% 29.44/29.70      (![X0 : $i, X1 : $i]:
% 29.44/29.70         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['19', '20'])).
% 29.44/29.70  thf(t4_subset, axiom,
% 29.44/29.70    (![A:$i,B:$i,C:$i]:
% 29.44/29.70     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 29.44/29.70       ( m1_subset_1 @ A @ C ) ))).
% 29.44/29.70  thf('22', plain,
% 29.44/29.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 29.44/29.70         (~ (r2_hidden @ X16 @ X17)
% 29.44/29.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 29.44/29.70          | (m1_subset_1 @ X16 @ X18))),
% 29.44/29.70      inference('cnf', [status(esa)], [t4_subset])).
% 29.44/29.70  thf('23', plain,
% 29.44/29.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.44/29.70         ((m1_subset_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 29.44/29.70          | ~ (r2_hidden @ X2 @ X1))),
% 29.44/29.70      inference('sup-', [status(thm)], ['21', '22'])).
% 29.44/29.70  thf('24', plain,
% 29.44/29.70      (![X0 : $i]: (m1_subset_1 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 29.44/29.70      inference('sup-', [status(thm)], ['18', '23'])).
% 29.44/29.70  thf(t2_subset, axiom,
% 29.44/29.70    (![A:$i,B:$i]:
% 29.44/29.70     ( ( m1_subset_1 @ A @ B ) =>
% 29.44/29.70       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 29.44/29.70  thf('25', plain,
% 29.44/29.70      (![X11 : $i, X12 : $i]:
% 29.44/29.70         ((r2_hidden @ X11 @ X12)
% 29.44/29.70          | (v1_xboole_0 @ X12)
% 29.44/29.70          | ~ (m1_subset_1 @ X11 @ X12))),
% 29.44/29.70      inference('cnf', [status(esa)], [t2_subset])).
% 29.44/29.70  thf('26', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         ((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ X0))
% 29.44/29.70          | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['24', '25'])).
% 29.44/29.70  thf('27', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('28', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | (m1_subset_1 @ (sk_D @ X27 @ X25 @ X26) @ 
% 29.44/29.70             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('29', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ 
% 29.44/29.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['27', '28'])).
% 29.44/29.70  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('32', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('33', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | ((sk_D @ X27 @ X25 @ X26) = (X27))
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('34', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | ((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['32', '33'])).
% 29.44/29.70  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('38', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1)))),
% 29.44/29.70      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 29.44/29.70  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('40', plain, (((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))),
% 29.44/29.70      inference('clc', [status(thm)], ['38', '39'])).
% 29.44/29.70  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('42', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 29.44/29.70      inference('demod', [status(thm)], ['29', '30', '31', '40', '41'])).
% 29.44/29.70  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('44', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('clc', [status(thm)], ['42', '43'])).
% 29.44/29.70  thf('45', plain,
% 29.44/29.70      (![X13 : $i, X14 : $i]:
% 29.44/29.70         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 29.44/29.70      inference('cnf', [status(esa)], [t3_subset])).
% 29.44/29.70  thf('46', plain, ((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('sup-', [status(thm)], ['44', '45'])).
% 29.44/29.70  thf(t12_xboole_1, axiom,
% 29.44/29.70    (![A:$i,B:$i]:
% 29.44/29.70     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 29.44/29.70  thf('47', plain,
% 29.44/29.70      (![X2 : $i, X3 : $i]:
% 29.44/29.70         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 29.44/29.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 29.44/29.70  thf('48', plain,
% 29.44/29.70      (((k2_xboole_0 @ sk_D_1 @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('sup-', [status(thm)], ['46', '47'])).
% 29.44/29.70  thf(commutativity_k2_xboole_0, axiom,
% 29.44/29.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 29.44/29.70  thf('49', plain,
% 29.44/29.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.44/29.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.44/29.70  thf('50', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('51', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | (m1_subset_1 @ (sk_D @ X27 @ X25 @ X26) @ 
% 29.44/29.70             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('52', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 29.44/29.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['50', '51'])).
% 29.44/29.70  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('55', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 29.44/29.70      inference('clc', [status(thm)], ['11', '12'])).
% 29.44/29.70  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('57', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 29.44/29.70      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 29.44/29.70  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('59', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('clc', [status(thm)], ['57', '58'])).
% 29.44/29.70  thf('60', plain,
% 29.44/29.70      (![X13 : $i, X14 : $i]:
% 29.44/29.70         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 29.44/29.70      inference('cnf', [status(esa)], [t3_subset])).
% 29.44/29.70  thf('61', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('sup-', [status(thm)], ['59', '60'])).
% 29.44/29.70  thf(t9_xboole_1, axiom,
% 29.44/29.70    (![A:$i,B:$i,C:$i]:
% 29.44/29.70     ( ( r1_tarski @ A @ B ) =>
% 29.44/29.70       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 29.44/29.70  thf('62', plain,
% 29.44/29.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 29.44/29.70         (~ (r1_tarski @ X6 @ X7)
% 29.44/29.70          | (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 29.44/29.70      inference('cnf', [status(esa)], [t9_xboole_1])).
% 29.44/29.70  thf('63', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         (r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ 
% 29.44/29.70          (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 29.44/29.70      inference('sup-', [status(thm)], ['61', '62'])).
% 29.44/29.70  thf('64', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         (r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ 
% 29.44/29.70          (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup+', [status(thm)], ['49', '63'])).
% 29.44/29.70  thf('65', plain,
% 29.44/29.70      ((r1_tarski @ (k2_xboole_0 @ sk_C @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('sup+', [status(thm)], ['48', '64'])).
% 29.44/29.70  thf('66', plain,
% 29.44/29.70      (![X13 : $i, X15 : $i]:
% 29.44/29.70         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 29.44/29.70      inference('cnf', [status(esa)], [t3_subset])).
% 29.44/29.70  thf('67', plain,
% 29.44/29.70      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['65', '66'])).
% 29.44/29.70  thf(t39_yellow_6, axiom,
% 29.44/29.70    (![A:$i]:
% 29.44/29.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.44/29.70       ( ![B:$i]:
% 29.44/29.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.44/29.70           ( ![C:$i]:
% 29.44/29.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.44/29.70               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 29.44/29.70                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 29.44/29.70  thf('68', plain,
% 29.44/29.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 29.44/29.70          | ~ (r2_hidden @ X28 @ X30)
% 29.44/29.70          | ~ (v3_pre_topc @ X30 @ X29)
% 29.44/29.70          | (r2_hidden @ X30 @ (u1_struct_0 @ (k9_yellow_6 @ X29 @ X28)))
% 29.44/29.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 29.44/29.70          | ~ (l1_pre_topc @ X29)
% 29.44/29.70          | ~ (v2_pre_topc @ X29)
% 29.44/29.70          | (v2_struct_0 @ X29))),
% 29.44/29.70      inference('cnf', [status(esa)], [t39_yellow_6])).
% 29.44/29.70  thf('69', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         ((v2_struct_0 @ sk_A)
% 29.44/29.70          | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70          | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 29.44/29.70          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)
% 29.44/29.70          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 29.44/29.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['67', '68'])).
% 29.44/29.70  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('72', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('clc', [status(thm)], ['42', '43'])).
% 29.44/29.70  thf('73', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('clc', [status(thm)], ['57', '58'])).
% 29.44/29.70  thf(fc7_tops_1, axiom,
% 29.44/29.70    (![A:$i,B:$i,C:$i]:
% 29.44/29.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 29.44/29.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 29.44/29.70         ( v3_pre_topc @ C @ A ) & 
% 29.44/29.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 29.44/29.70       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 29.44/29.70  thf('74', plain,
% 29.44/29.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 29.44/29.70          | ~ (v3_pre_topc @ X22 @ X23)
% 29.44/29.70          | ~ (l1_pre_topc @ X23)
% 29.44/29.70          | ~ (v2_pre_topc @ X23)
% 29.44/29.70          | ~ (v3_pre_topc @ X24 @ X23)
% 29.44/29.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 29.44/29.70          | (v3_pre_topc @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 29.44/29.70      inference('cnf', [status(esa)], [fc7_tops_1])).
% 29.44/29.70  thf('75', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 29.44/29.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.44/29.70          | ~ (v3_pre_topc @ X0 @ sk_A)
% 29.44/29.70          | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70          | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 29.44/29.70      inference('sup-', [status(thm)], ['73', '74'])).
% 29.44/29.70  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('78', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 29.44/29.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.44/29.70          | ~ (v3_pre_topc @ X0 @ sk_A)
% 29.44/29.70          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 29.44/29.70      inference('demod', [status(thm)], ['75', '76', '77'])).
% 29.44/29.70  thf('79', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('80', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | (v3_pre_topc @ (sk_D @ X27 @ X25 @ X26) @ X26)
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('81', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['79', '80'])).
% 29.44/29.70  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('84', plain, (((sk_D @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 29.44/29.70      inference('clc', [status(thm)], ['11', '12'])).
% 29.44/29.70  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('86', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 29.44/29.70      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 29.44/29.70  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('88', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 29.44/29.70      inference('clc', [status(thm)], ['86', '87'])).
% 29.44/29.70  thf('89', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 29.44/29.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.44/29.70          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 29.44/29.70      inference('demod', [status(thm)], ['78', '88'])).
% 29.44/29.70  thf('90', plain,
% 29.44/29.70      ((~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 29.44/29.70        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A))),
% 29.44/29.70      inference('sup-', [status(thm)], ['72', '89'])).
% 29.44/29.70  thf('91', plain,
% 29.44/29.70      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('92', plain,
% 29.44/29.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 29.44/29.70         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 29.44/29.70          | (v3_pre_topc @ (sk_D @ X27 @ X25 @ X26) @ X26)
% 29.44/29.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 29.44/29.70          | ~ (l1_pre_topc @ X26)
% 29.44/29.70          | ~ (v2_pre_topc @ X26)
% 29.44/29.70          | (v2_struct_0 @ X26))),
% 29.44/29.70      inference('cnf', [status(esa)], [t38_yellow_6])).
% 29.44/29.70  thf('93', plain,
% 29.44/29.70      (((v2_struct_0 @ sk_A)
% 29.44/29.70        | ~ (v2_pre_topc @ sk_A)
% 29.44/29.70        | ~ (l1_pre_topc @ sk_A)
% 29.44/29.70        | (v3_pre_topc @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A)
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['91', '92'])).
% 29.44/29.70  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('96', plain, (((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))),
% 29.44/29.70      inference('clc', [status(thm)], ['38', '39'])).
% 29.44/29.70  thf('97', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('98', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 29.44/29.70      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 29.44/29.70  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('100', plain, ((v3_pre_topc @ sk_D_1 @ sk_A)),
% 29.44/29.70      inference('clc', [status(thm)], ['98', '99'])).
% 29.44/29.70  thf('101', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A)),
% 29.44/29.70      inference('demod', [status(thm)], ['90', '100'])).
% 29.44/29.70  thf('102', plain,
% 29.44/29.70      (![X0 : $i]:
% 29.44/29.70         ((v2_struct_0 @ sk_A)
% 29.44/29.70          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 29.44/29.70          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 29.44/29.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 29.44/29.70      inference('demod', [status(thm)], ['69', '70', '71', '101'])).
% 29.44/29.70  thf('103', plain,
% 29.44/29.70      (((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 29.44/29.70        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 29.44/29.70        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 29.44/29.70        | (v2_struct_0 @ sk_A))),
% 29.44/29.70      inference('sup-', [status(thm)], ['26', '102'])).
% 29.44/29.70  thf('104', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('105', plain,
% 29.44/29.70      (((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 29.44/29.70        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 29.44/29.70        | (v2_struct_0 @ sk_A))),
% 29.44/29.70      inference('demod', [status(thm)], ['103', '104'])).
% 29.44/29.70  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('107', plain,
% 29.44/29.70      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 29.44/29.70        | (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 29.44/29.70      inference('clc', [status(thm)], ['105', '106'])).
% 29.44/29.70  thf(t1_subset, axiom,
% 29.44/29.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 29.44/29.70  thf('108', plain,
% 29.44/29.70      (![X9 : $i, X10 : $i]:
% 29.44/29.70         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 29.44/29.70      inference('cnf', [status(esa)], [t1_subset])).
% 29.44/29.70  thf('109', plain,
% 29.44/29.70      (((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 29.44/29.70        | (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 29.44/29.70      inference('sup-', [status(thm)], ['107', '108'])).
% 29.44/29.70  thf('110', plain,
% 29.44/29.70      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 29.44/29.70          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 29.44/29.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.44/29.70  thf('111', plain, ((v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_D_1))),
% 29.44/29.70      inference('clc', [status(thm)], ['109', '110'])).
% 29.44/29.70  thf('112', plain,
% 29.44/29.70      (![X0 : $i, X1 : $i]:
% 29.44/29.70         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.44/29.70      inference('sup-', [status(thm)], ['19', '20'])).
% 29.44/29.70  thf(t5_subset, axiom,
% 29.44/29.70    (![A:$i,B:$i,C:$i]:
% 29.44/29.70     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 29.44/29.70          ( v1_xboole_0 @ C ) ) ))).
% 29.44/29.70  thf('113', plain,
% 29.44/29.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 29.44/29.70         (~ (r2_hidden @ X19 @ X20)
% 29.44/29.70          | ~ (v1_xboole_0 @ X21)
% 29.44/29.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 29.44/29.70      inference('cnf', [status(esa)], [t5_subset])).
% 29.44/29.70  thf('114', plain,
% 29.44/29.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.44/29.70         (~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 29.44/29.70      inference('sup-', [status(thm)], ['112', '113'])).
% 29.44/29.70  thf('115', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 29.44/29.70      inference('sup-', [status(thm)], ['111', '114'])).
% 29.44/29.70  thf('116', plain, ($false), inference('sup-', [status(thm)], ['17', '115'])).
% 29.44/29.70  
% 29.44/29.70  % SZS output end Refutation
% 29.44/29.70  
% 29.53/29.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
