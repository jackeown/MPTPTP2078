%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rzosrEfmhg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 184 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  696 (2392 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ ( k2_pre_topc @ X19 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v2_tex_2 @ ( sk_C @ X15 @ X16 ) @ X16 )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ ( sk_C @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','20','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( sk_C @ sk_B @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( sk_C @ X15 @ X16 ) )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v1_tops_1 @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','38','44','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( X15
       != ( sk_C @ X15 @ X16 ) )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rzosrEfmhg
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 72 iterations in 0.036s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(t48_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.48             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.48                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d7_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.48             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.48               ( ![C:$i]:
% 0.20/0.48                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.48                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ X15 @ X16) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | (v3_tex_2 @ X15 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.48  thf('8', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(t41_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( r1_tarski @ C @ B ) =>
% 0.20/0.48                   ( ( k9_subset_1 @
% 0.20/0.48                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.20/0.48                     ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.48          | ~ (v2_tex_2 @ X18 @ X19)
% 0.20/0.48          | ~ (r1_tarski @ X20 @ X18)
% 0.20/0.48          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ 
% 0.20/0.48              (k2_pre_topc @ X19 @ X20)) = (X20))
% 0.20/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.48          | ~ (l1_pre_topc @ X19)
% 0.20/0.48          | ~ (v2_pre_topc @ X19)
% 0.20/0.48          | (v2_struct_0 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.48          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(commutativity_k9_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48           = (k3_xboole_0 @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.48          | (v2_tex_2 @ (sk_C @ X15 @ X16) @ X16)
% 0.20/0.48          | (v3_tex_2 @ X15 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.48  thf('27', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48              = (X0))
% 0.20/0.48          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13', '20', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48            = (sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.48          | (r1_tarski @ X15 @ (sk_C @ X15 @ X16))
% 0.20/0.48          | (v3_tex_2 @ X15 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.48        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.48  thf('37', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d2_tops_3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.48             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.48          | ~ (v1_tops_1 @ X13 @ X14)
% 0.20/0.48          | ((k2_pre_topc @ X14 @ X13) = (u1_struct_0 @ X14))
% 0.20/0.48          | ~ (l1_pre_topc @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(t3_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('47', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf(t28_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.48         = (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48         = (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, ((((sk_C @ sk_B @ sk_A) = (sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '38', '44', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.48          | ((X15) != (sk_C @ X15 @ X16))
% 0.20/0.48          | (v3_tex_2 @ X15 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.48  thf('59', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['52', '60'])).
% 0.20/0.48  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
