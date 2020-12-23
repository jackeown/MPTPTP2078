%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HSCZuG4VXc

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:10 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 186 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  801 (2062 expanded)
%              Number of equality atoms :   42 (  52 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( m1_subset_1 @ ( sk_C @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_tex_2 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_tex_2 @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X31 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_pre_topc @ X32 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( v2_tex_2 @ ( sk_C @ X28 @ X29 ) @ X29 )
      | ( v3_tex_2 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( r1_tarski @ X28 @ ( sk_C @ X28 @ X29 ) )
      | ( v3_tex_2 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v1_tops_1 @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','64'])).

thf('66',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','65'])).

thf('67',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','31','37','42','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( X28
       != ( sk_C @ X28 @ X29 ) )
      | ( v3_tex_2 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['67','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HSCZuG4VXc
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 215 iterations in 0.095s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.38/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.56  thf(t48_tex_2, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.38/0.56             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56            ( l1_pre_topc @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.38/0.56                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.38/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d7_tex_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.56             ( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.56               ( ![C:$i]:
% 0.38/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.56                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X28 : $i, X29 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.56          | ~ (v2_tex_2 @ X28 @ X29)
% 0.38/0.56          | (m1_subset_1 @ (sk_C @ X28 @ X29) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.56          | (v3_tex_2 @ X28 @ X29)
% 0.38/0.56          | ~ (l1_pre_topc @ X29))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.56        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('6', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.56        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.38/0.56  thf('8', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf(t41_tex_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.38/0.56             ( ![C:$i]:
% 0.38/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56                 ( ( r1_tarski @ C @ B ) =>
% 0.38/0.56                   ( ( k9_subset_1 @
% 0.38/0.56                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.38/0.56                     ( C ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.38/0.56          | ~ (v2_tex_2 @ X31 @ X32)
% 0.38/0.56          | ~ (r1_tarski @ X33 @ X31)
% 0.38/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.38/0.56              (k2_pre_topc @ X32 @ X33)) = (X33))
% 0.38/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.38/0.56          | ~ (l1_pre_topc @ X32)
% 0.38/0.56          | ~ (v2_pre_topc @ X32)
% 0.38/0.56          | (v2_struct_0 @ X32))),
% 0.38/0.56      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_A)
% 0.38/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.56          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.56          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X28 : $i, X29 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.56          | ~ (v2_tex_2 @ X28 @ X29)
% 0.38/0.56          | (v2_tex_2 @ (sk_C @ X28 @ X29) @ X29)
% 0.38/0.56          | (v3_tex_2 @ X28 @ X29)
% 0.38/0.56          | ~ (l1_pre_topc @ X29))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.56        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('18', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.38/0.56  thf('20', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('21', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.57              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.57          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12', '13', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.57            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.38/0.57        | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X28 : $i, X29 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.57          | ~ (v2_tex_2 @ X28 @ X29)
% 0.38/0.57          | (r1_tarski @ X28 @ (sk_C @ X28 @ X29))
% 0.38/0.57          | (v3_tex_2 @ X28 @ X29)
% 0.38/0.57          | ~ (l1_pre_topc @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.57        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.57        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('28', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.38/0.57  thf('30', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d2_tops_3, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.38/0.57             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X26 : $i, X27 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.57          | ~ (v1_tops_1 @ X26 @ X27)
% 0.38/0.57          | ((k2_pre_topc @ X27 @ X26) = (u1_struct_0 @ X27))
% 0.38/0.57          | ~ (l1_pre_topc @ X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('36', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('37', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.38/0.57  thf(dt_k2_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.57  thf('39', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.57  thf('40', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.57  thf(redefinition_k9_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf(t3_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i]:
% 0.38/0.57         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.57  thf('45', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf(l32_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X3 : $i, X5 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (((k4_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.57         = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.57  thf(t48_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.38/0.57           = (k3_xboole_0 @ X6 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (((k4_xboole_0 @ (sk_C @ sk_B @ sk_A) @ k1_xboole_0)
% 0.38/0.57         = (k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf(t4_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf(d5_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.38/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.57  thf('53', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i]:
% 0.38/0.57         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.57  thf('56', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.38/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.57      inference('simplify', [status(thm)], ['59'])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (![X3 : $i, X5 : $i]:
% 0.38/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.57  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.57  thf('63', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['58', '62'])).
% 0.38/0.57  thf('64', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['55', '63'])).
% 0.38/0.57  thf('65', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['52', '64'])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      (((sk_C @ sk_B @ sk_A)
% 0.38/0.57         = (k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['49', '65'])).
% 0.38/0.57  thf('67', plain, ((((sk_C @ sk_B @ sk_A) = (sk_B)) | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['23', '31', '37', '42', '66'])).
% 0.38/0.57  thf('68', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('69', plain,
% 0.38/0.57      (![X28 : $i, X29 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.57          | ~ (v2_tex_2 @ X28 @ X29)
% 0.38/0.57          | ((X28) != (sk_C @ X28 @ X29))
% 0.38/0.57          | (v3_tex_2 @ X28 @ X29)
% 0.38/0.57          | ~ (l1_pre_topc @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.57        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.38/0.57        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.57  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('72', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('73', plain,
% 0.38/0.57      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.38/0.57  thf('74', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('75', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['73', '74'])).
% 0.38/0.57  thf('76', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['67', '75'])).
% 0.38/0.57  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
