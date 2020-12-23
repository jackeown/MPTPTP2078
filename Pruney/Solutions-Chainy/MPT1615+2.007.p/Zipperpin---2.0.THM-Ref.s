%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VUvCd1cWEY

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 108 expanded)
%              Number of leaves         :   49 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  532 ( 636 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X44: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ( zip_tseitin_5 @ X46 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) )
      | ( zip_tseitin_4 @ X41 @ X42 )
      | ~ ( zip_tseitin_5 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X38 @ ( u1_pre_topc @ X39 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X39 ) @ X38 ) @ ( u1_pre_topc @ X39 ) )
      | ~ ( zip_tseitin_4 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k5_setfam_1 @ X14 @ X13 )
        = ( k3_tarski @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ k1_xboole_0 )
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ k1_xboole_0 )
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_tarski @ X8 @ X6 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X47 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X47 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X47: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X47 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X47 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t23_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t23_yellow_1])).

thf('39',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VUvCd1cWEY
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 166 iterations in 0.081s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.53  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.53  thf(d1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.53         ( ( ![B:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ![C:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.53                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.53                     ( r2_hidden @
% 0.20/0.53                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.20/0.53                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.20/0.53           ( ![B:$i]:
% 0.20/0.53             ( ( m1_subset_1 @
% 0.20/0.53                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.53                 ( r2_hidden @
% 0.20/0.53                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.53                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.20/0.53           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_1, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.20/0.53       ( ( m1_subset_1 @
% 0.20/0.53           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_3, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.20/0.53       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.53         ( r2_hidden @
% 0.20/0.53           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_5, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.20/0.53       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_7, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.20/0.53       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_9, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.20/0.53       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.53         ( r2_hidden @
% 0.20/0.53           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_11, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.20/0.53       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.53         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_12, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.53         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.53           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.20/0.53           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X44 : $i, X46 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X44)
% 0.20/0.53          | (zip_tseitin_5 @ X46 @ X44)
% 0.20/0.53          | ~ (l1_pre_topc @ X44))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.20/0.53  thf(t4_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X41 : $i, X42 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X41 @ 
% 0.20/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42))))
% 0.20/0.53          | (zip_tseitin_4 @ X41 @ X42)
% 0.20/0.53          | ~ (zip_tseitin_5 @ X41 @ X42))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (zip_tseitin_5 @ k1_xboole_0 @ X0)
% 0.20/0.53          | (zip_tseitin_4 @ k1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | (zip_tseitin_4 @ k1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('5', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X38 @ (u1_pre_topc @ X39))
% 0.20/0.53          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X39) @ X38) @ 
% 0.20/0.53             (u1_pre_topc @ X39))
% 0.20/0.53          | ~ (zip_tseitin_4 @ X38 @ X39))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (zip_tseitin_4 @ k1_xboole_0 @ X0)
% 0.20/0.53          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.20/0.53             (u1_pre_topc @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(redefinition_k5_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((k5_setfam_1 @ X14 @ X13) = (k3_tarski @ X13))
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k5_setfam_1 @ X0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(dt_k5_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k5_setfam_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k5_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k5_setfam_1 @ X0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k3_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t2_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((r2_hidden @ X15 @ X16)
% 0.20/0.53          | (v1_xboole_0 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (r2_hidden @ (k3_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf(d1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.53          | (r2_hidden @ X5 @ X7)
% 0.20/0.53          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.53  thf(d1_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i]: (r2_hidden @ (k3_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.20/0.53          | (r1_tarski @ X8 @ X6)
% 0.20/0.53          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X6 : $i, X8 : $i]:
% 0.20/0.53         ((r1_tarski @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.53  thf('27', plain, (![X0 : $i]: (r1_tarski @ (k3_tarski @ k1_xboole_0) @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]: ((k5_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (zip_tseitin_4 @ k1_xboole_0 @ X0)
% 0.20/0.53          | (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '33'])).
% 0.20/0.53  thf(t13_yellow_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.53         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X47 : $i]:
% 0.20/0.53         (~ (r2_hidden @ k1_xboole_0 @ X47)
% 0.20/0.53          | ((k3_yellow_0 @ (k2_yellow_1 @ X47)) = (k1_xboole_0))
% 0.20/0.53          | (v1_xboole_0 @ X47))),
% 0.20/0.53      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X47 : $i]:
% 0.20/0.53         (((k3_yellow_0 @ (k2_yellow_1 @ X47)) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ k1_xboole_0 @ X47))),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.53  thf(t23_yellow_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.53         ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf(zf_stmt_13, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.53            ( k1_xboole_0 ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.53  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
