%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KFjY47ubal

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 157 expanded)
%              Number of leaves         :   30 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  673 (1879 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t48_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v1_tops_1 @ B @ A )
                & ( v2_tex_2 @ B @ A ) )
             => ( v3_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v2_tex_2 @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( r1_tarski @ X16 @ ( sk_C @ X16 @ X17 ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','31','37','42','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( X16
       != ( sk_C @ X16 @ X17 ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['52','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KFjY47ubal
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 119 iterations in 0.071s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(t48_tex_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.54             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54            ( l1_pre_topc @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.54                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.22/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d7_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.54               ( ![C:$i]:
% 0.22/0.54                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.54                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.54          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | (v3_tex_2 @ X16 @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('6', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.54  thf('8', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf(t41_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ![C:$i]:
% 0.22/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                 ( ( r1_tarski @ C @ B ) =>
% 0.22/0.54                   ( ( k9_subset_1 @
% 0.22/0.54                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.22/0.54                     ( C ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.54          | ~ (v2_tex_2 @ X19 @ X20)
% 0.22/0.54          | ~ (r1_tarski @ X21 @ X19)
% 0.22/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.22/0.54              (k2_pre_topc @ X20 @ X21)) = (X21))
% 0.22/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.54          | ~ (l1_pre_topc @ X20)
% 0.22/0.54          | ~ (v2_pre_topc @ X20)
% 0.22/0.54          | (v2_struct_0 @ X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.22/0.54          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.54          | (v2_tex_2 @ (sk_C @ X16 @ X17) @ X17)
% 0.22/0.54          | (v3_tex_2 @ X16 @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.54        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('18', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.54  thf('20', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('21', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.54      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['11', '12', '13', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '22'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.54          | (r1_tarski @ X16 @ (sk_C @ X16 @ X17))
% 0.22/0.54          | (v3_tex_2 @ X16 @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.54        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('28', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.54  thf('30', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('31', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.22/0.54      inference('clc', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d2_tops_3, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v1_tops_1 @ B @ A ) <=>
% 0.22/0.54             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.54          | ~ (v1_tops_1 @ X14 @ X15)
% 0.22/0.54          | ((k2_pre_topc @ X15 @ X14) = (u1_struct_0 @ X15))
% 0.22/0.54          | ~ (l1_pre_topc @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('36', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('37', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.54  thf(dt_k2_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.54  thf('39', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('40', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.22/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.22/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X11 : $i, X12 : $i]:
% 0.22/0.54         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('45', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf(l32_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (((k4_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.54         = (k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf(t48_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.22/0.54           = (k3_xboole_0 @ X4 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (((k4_xboole_0 @ (sk_C @ sk_B @ sk_A) @ k1_xboole_0)
% 0.22/0.54         = (k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.54  thf(t3_boole, axiom,
% 0.22/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.54  thf('50', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (((sk_C @ sk_B @ sk_A)
% 0.22/0.54         = (k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.54  thf('52', plain, ((((sk_C @ sk_B @ sk_A) = (sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '31', '37', '42', '51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.22/0.54          | ((X16) != (sk_C @ X16 @ X17))
% 0.22/0.54          | (v3_tex_2 @ X16 @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.22/0.54        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.54  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('57', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.22/0.54  thf('59', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('60', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.22/0.54      inference('clc', [status(thm)], ['58', '59'])).
% 0.22/0.54  thf('61', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['52', '60'])).
% 0.22/0.54  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
