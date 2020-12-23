%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RlNdB09gy0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:21 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 231 expanded)
%              Number of leaves         :   46 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  660 (1949 expanded)
%              Number of equality atoms :   17 (  62 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X39 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X36: $i,X38: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( zip_tseitin_5 @ X38 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X39 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ( zip_tseitin_4 @ X33 @ X34 )
      | ~ ( zip_tseitin_5 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ ( u1_pre_topc @ X31 ) )
      | ~ ( zip_tseitin_4 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X36: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( r2_hidden @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('29',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X14 @ X17 )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( r2_hidden @ X14 @ ( u1_pre_topc @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ ( u1_pre_topc @ X15 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('36',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('38',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('44',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X40 ) @ X40 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X40 ) )
        = ( k3_tarski @ X40 ) )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X40: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X40 ) )
        = ( k3_tarski @ X40 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X40 ) @ X40 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('49',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('50',plain,
    ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RlNdB09gy0
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:27:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 665 iterations in 0.313s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.55/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.75  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.55/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.75  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.55/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.75  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.55/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.55/0.75  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.55/0.75  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.55/0.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.55/0.75  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.55/0.75  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.55/0.75  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.55/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.75  thf(t94_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.55/0.75       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.55/0.75  thf('0', plain,
% 0.55/0.75      (![X8 : $i, X9 : $i]:
% 0.55/0.75         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 0.55/0.75          | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.55/0.75  thf(dt_u1_pre_topc, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( l1_pre_topc @ A ) =>
% 0.55/0.75       ( m1_subset_1 @
% 0.55/0.75         ( u1_pre_topc @ A ) @ 
% 0.55/0.75         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      (![X39 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (u1_pre_topc @ X39) @ 
% 0.55/0.75           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39))))
% 0.55/0.75          | ~ (l1_pre_topc @ X39))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.55/0.75  thf(l3_subset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.75         (~ (r2_hidden @ X11 @ X12)
% 0.55/0.75          | (r2_hidden @ X11 @ X13)
% 0.55/0.75          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.55/0.75      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X0)
% 0.55/0.75          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.75          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.75  thf('4', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 0.55/0.75          | (r2_hidden @ (sk_C @ X1 @ (u1_pre_topc @ X0)) @ 
% 0.55/0.75             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.75          | ~ (l1_pre_topc @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['0', '3'])).
% 0.55/0.75  thf(l49_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.55/0.75  thf('5', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i]:
% 0.55/0.75         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.55/0.75      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X0)
% 0.55/0.75          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 0.55/0.75          | (r1_tarski @ (sk_C @ X1 @ (u1_pre_topc @ X0)) @ 
% 0.55/0.75             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.75  thf(t99_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.55/0.75  thf('7', plain, (![X10 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X10)) = (X10))),
% 0.55/0.75      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.55/0.75  thf('8', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X0)
% 0.55/0.75          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 0.55/0.75          | (r1_tarski @ (sk_C @ X1 @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['6', '7'])).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      (![X8 : $i, X9 : $i]:
% 0.55/0.75         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 0.55/0.75          | ~ (r1_tarski @ (sk_C @ X9 @ X8) @ X9))),
% 0.55/0.75      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.55/0.75  thf('10', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0))
% 0.55/0.75          | ~ (l1_pre_topc @ X0)
% 0.55/0.75          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X0)
% 0.55/0.75          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['10'])).
% 0.55/0.75  thf(t24_yellow_1, conjecture,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.75       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.55/0.75         ( u1_struct_0 @ A ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i]:
% 0.55/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.75            ( l1_pre_topc @ A ) ) =>
% 0.55/0.75          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.55/0.75            ( u1_struct_0 @ A ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.55/0.75  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(d1_pre_topc, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( l1_pre_topc @ A ) =>
% 0.55/0.75       ( ( v2_pre_topc @ A ) <=>
% 0.55/0.75         ( ( ![B:$i]:
% 0.55/0.75             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.75               ( ![C:$i]:
% 0.55/0.75                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.75                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.55/0.75                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.55/0.75                     ( r2_hidden @
% 0.55/0.75                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.55/0.75                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.55/0.75           ( ![B:$i]:
% 0.55/0.75             ( ( m1_subset_1 @
% 0.55/0.75                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.75               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.55/0.75                 ( r2_hidden @
% 0.55/0.75                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.55/0.75                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.55/0.75           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_2, axiom,
% 0.55/0.75    (![B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.55/0.75       ( ( m1_subset_1 @
% 0.55/0.75           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.75         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.55/0.75  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_4, axiom,
% 0.55/0.75    (![B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.55/0.75       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.55/0.75         ( r2_hidden @
% 0.55/0.75           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_6, axiom,
% 0.55/0.75    (![B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.55/0.75       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.75         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_8, axiom,
% 0.55/0.75    (![C:$i,B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.55/0.75       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.75         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.55/0.75  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_10, axiom,
% 0.55/0.75    (![C:$i,B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.55/0.75       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.55/0.75         ( r2_hidden @
% 0.55/0.75           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_12, axiom,
% 0.55/0.75    (![C:$i,B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.55/0.75       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.55/0.75         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_13, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( l1_pre_topc @ A ) =>
% 0.55/0.75       ( ( v2_pre_topc @ A ) <=>
% 0.55/0.75         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.55/0.75           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.55/0.75           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X36 : $i, X38 : $i]:
% 0.55/0.75         (~ (v2_pre_topc @ X36)
% 0.55/0.75          | (zip_tseitin_5 @ X38 @ X36)
% 0.55/0.75          | ~ (l1_pre_topc @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.75  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('16', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)], ['14', '15'])).
% 0.55/0.75  thf('17', plain,
% 0.55/0.75      (![X39 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (u1_pre_topc @ X39) @ 
% 0.55/0.75           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39))))
% 0.55/0.75          | ~ (l1_pre_topc @ X39))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.55/0.75  thf('18', plain,
% 0.55/0.75      (![X33 : $i, X34 : $i]:
% 0.55/0.75         (~ (m1_subset_1 @ X33 @ 
% 0.55/0.75             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 0.55/0.75          | (zip_tseitin_4 @ X33 @ X34)
% 0.55/0.75          | ~ (zip_tseitin_5 @ X33 @ X34))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.75  thf('19', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X0)
% 0.55/0.75          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 0.55/0.75          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['16', '19'])).
% 0.55/0.75  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('22', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.55/0.75  thf(d10_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.75  thf('23', plain,
% 0.55/0.75      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.55/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.75  thf('24', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.55/0.75      inference('simplify', [status(thm)], ['23'])).
% 0.55/0.75  thf('25', plain,
% 0.55/0.75      (![X30 : $i, X31 : $i]:
% 0.55/0.75         (~ (r1_tarski @ X30 @ (u1_pre_topc @ X31))
% 0.55/0.75          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X31) @ X30) @ 
% 0.55/0.75             (u1_pre_topc @ X31))
% 0.55/0.75          | ~ (zip_tseitin_4 @ X30 @ X31))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.55/0.75          | (r2_hidden @ 
% 0.55/0.75             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.55/0.75             (u1_pre_topc @ X0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.75  thf('27', plain,
% 0.55/0.75      ((r2_hidden @ 
% 0.55/0.75        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.55/0.75        (u1_pre_topc @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['22', '26'])).
% 0.55/0.75  thf('28', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (~ (v2_pre_topc @ X36)
% 0.55/0.75          | (r2_hidden @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))
% 0.55/0.75          | ~ (l1_pre_topc @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.55/0.75         ((zip_tseitin_0 @ X16 @ X14 @ X17)
% 0.55/0.75          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.55/0.75          | ~ (r2_hidden @ X14 @ (u1_pre_topc @ X17)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.55/0.75  thf('30', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X0)
% 0.55/0.75          | ~ (v2_pre_topc @ X0)
% 0.55/0.75          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 0.55/0.75          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.75  thf('31', plain,
% 0.55/0.75      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 0.55/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.55/0.75        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['27', '30'])).
% 0.55/0.75  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('34', plain,
% 0.55/0.75      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.75         ((r2_hidden @ X16 @ (u1_pre_topc @ X15))
% 0.55/0.75          | ~ (zip_tseitin_0 @ X16 @ X14 @ X15))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.55/0.75  thf('36', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i]:
% 0.55/0.75         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.55/0.75      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (![X3 : $i, X5 : $i]:
% 0.55/0.75         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.55/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.75  thf('40', plain,
% 0.55/0.75      ((~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 0.55/0.75           (u1_struct_0 @ sk_A))
% 0.55/0.75        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.75        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['11', '40'])).
% 0.55/0.75  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('43', plain,
% 0.55/0.75      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['41', '42'])).
% 0.55/0.75  thf(t14_yellow_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.75       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.55/0.75         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.55/0.75  thf('44', plain,
% 0.55/0.75      (![X40 : $i]:
% 0.55/0.75         (~ (r2_hidden @ (k3_tarski @ X40) @ X40)
% 0.55/0.75          | ((k4_yellow_0 @ (k2_yellow_1 @ X40)) = (k3_tarski @ X40))
% 0.55/0.75          | (v1_xboole_0 @ X40))),
% 0.55/0.75      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.55/0.75  thf(d1_xboole_0, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.75  thf('45', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      (![X40 : $i]:
% 0.55/0.75         (((k4_yellow_0 @ (k2_yellow_1 @ X40)) = (k3_tarski @ X40))
% 0.55/0.75          | ~ (r2_hidden @ (k3_tarski @ X40) @ X40))),
% 0.55/0.75      inference('clc', [status(thm)], ['44', '45'])).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.55/0.75        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.55/0.75            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['43', '46'])).
% 0.55/0.75  thf('48', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['41', '42'])).
% 0.55/0.75  thf('50', plain,
% 0.55/0.75      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.55/0.75         = (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.55/0.75         != (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('52', plain, ($false),
% 0.55/0.75      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
