%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lhVnZ9E3jE

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:20 EST 2020

% Result     : Theorem 7.94s
% Output     : Refutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 231 expanded)
%              Number of leaves         :   47 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  653 (1919 expanded)
%              Number of equality atoms :   17 (  62 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( u1_pre_topc @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X12 ) @ ( k3_tarski @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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
    ! [X40: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( zip_tseitin_5 @ X42 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) )
      | ( zip_tseitin_4 @ X37 @ X38 )
      | ~ ( zip_tseitin_5 @ X37 @ X38 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X34 @ ( u1_pre_topc @ X35 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X35 ) @ X34 ) @ ( u1_pre_topc @ X35 ) )
      | ~ ( zip_tseitin_4 @ X34 @ X35 ) ) ),
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
    ! [X40: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( r2_hidden @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('29',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X18 @ X21 )
      | ~ ( r2_hidden @ X20 @ ( u1_pre_topc @ X21 ) )
      | ~ ( r2_hidden @ X18 @ ( u1_pre_topc @ X21 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X20 @ ( u1_pre_topc @ X19 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('36',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('38',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X44: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X44 ) @ X44 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X44 ) )
        = ( k3_tarski @ X44 ) )
      | ( v1_xboole_0 @ X44 ) ) ),
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
    ! [X44: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X44 ) )
        = ( k3_tarski @ X44 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X44 ) @ X44 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lhVnZ9E3jE
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.94/8.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.94/8.15  % Solved by: fo/fo7.sh
% 7.94/8.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.94/8.15  % done 3847 iterations in 7.705s
% 7.94/8.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.94/8.15  % SZS output start Refutation
% 7.94/8.15  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 7.94/8.15  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 7.94/8.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.94/8.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.94/8.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.94/8.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.94/8.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 7.94/8.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.94/8.15  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 7.94/8.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.94/8.15  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 7.94/8.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.94/8.15  thf(sk_A_type, type, sk_A: $i).
% 7.94/8.15  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.94/8.15  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.94/8.15  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 7.94/8.15  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 7.94/8.15  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 7.94/8.15  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 7.94/8.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.94/8.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.94/8.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.94/8.15  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 7.94/8.15  thf(d3_tarski, axiom,
% 7.94/8.15    (![A:$i,B:$i]:
% 7.94/8.15     ( ( r1_tarski @ A @ B ) <=>
% 7.94/8.15       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.94/8.15  thf('0', plain,
% 7.94/8.15      (![X4 : $i, X6 : $i]:
% 7.94/8.15         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 7.94/8.15      inference('cnf', [status(esa)], [d3_tarski])).
% 7.94/8.15  thf(dt_u1_pre_topc, axiom,
% 7.94/8.15    (![A:$i]:
% 7.94/8.15     ( ( l1_pre_topc @ A ) =>
% 7.94/8.15       ( m1_subset_1 @
% 7.94/8.15         ( u1_pre_topc @ A ) @ 
% 7.94/8.15         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 7.94/8.15  thf('1', plain,
% 7.94/8.15      (![X43 : $i]:
% 7.94/8.15         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 7.94/8.15           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 7.94/8.15          | ~ (l1_pre_topc @ X43))),
% 7.94/8.15      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 7.94/8.15  thf(l3_subset_1, axiom,
% 7.94/8.15    (![A:$i,B:$i]:
% 7.94/8.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.94/8.15       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 7.94/8.15  thf('2', plain,
% 7.94/8.15      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.94/8.15         (~ (r2_hidden @ X15 @ X16)
% 7.94/8.15          | (r2_hidden @ X15 @ X17)
% 7.94/8.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 7.94/8.15      inference('cnf', [status(esa)], [l3_subset_1])).
% 7.94/8.15  thf('3', plain,
% 7.94/8.15      (![X0 : $i, X1 : $i]:
% 7.94/8.15         (~ (l1_pre_topc @ X0)
% 7.94/8.15          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.94/8.15          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 7.94/8.15      inference('sup-', [status(thm)], ['1', '2'])).
% 7.94/8.15  thf('4', plain,
% 7.94/8.15      (![X0 : $i, X1 : $i]:
% 7.94/8.15         ((r1_tarski @ (u1_pre_topc @ X0) @ X1)
% 7.94/8.15          | (r2_hidden @ (sk_C @ X1 @ (u1_pre_topc @ X0)) @ 
% 7.94/8.15             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.94/8.15          | ~ (l1_pre_topc @ X0))),
% 7.94/8.15      inference('sup-', [status(thm)], ['0', '3'])).
% 7.94/8.15  thf('5', plain,
% 7.94/8.15      (![X4 : $i, X6 : $i]:
% 7.94/8.15         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 7.94/8.15      inference('cnf', [status(esa)], [d3_tarski])).
% 7.94/8.15  thf('6', plain,
% 7.94/8.15      (![X0 : $i]:
% 7.94/8.15         (~ (l1_pre_topc @ X0)
% 7.94/8.15          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 7.94/8.15             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.94/8.15          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 7.94/8.15             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 7.94/8.15      inference('sup-', [status(thm)], ['4', '5'])).
% 7.94/8.15  thf('7', plain,
% 7.94/8.15      (![X0 : $i]:
% 7.94/8.15         ((r1_tarski @ (u1_pre_topc @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 7.94/8.15          | ~ (l1_pre_topc @ X0))),
% 7.94/8.15      inference('simplify', [status(thm)], ['6'])).
% 7.94/8.15  thf(t95_zfmisc_1, axiom,
% 7.94/8.15    (![A:$i,B:$i]:
% 7.94/8.15     ( ( r1_tarski @ A @ B ) =>
% 7.94/8.15       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 7.94/8.15  thf('8', plain,
% 7.94/8.15      (![X12 : $i, X13 : $i]:
% 7.94/8.15         ((r1_tarski @ (k3_tarski @ X12) @ (k3_tarski @ X13))
% 7.94/8.15          | ~ (r1_tarski @ X12 @ X13))),
% 7.94/8.15      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 7.94/8.15  thf('9', plain,
% 7.94/8.15      (![X0 : $i]:
% 7.94/8.15         (~ (l1_pre_topc @ X0)
% 7.94/8.15          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 7.94/8.15             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 7.94/8.15      inference('sup-', [status(thm)], ['7', '8'])).
% 7.94/8.15  thf(t99_zfmisc_1, axiom,
% 7.94/8.15    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 7.94/8.15  thf('10', plain, (![X14 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X14)) = (X14))),
% 7.94/8.15      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 7.94/8.15  thf('11', plain,
% 7.94/8.15      (![X0 : $i]:
% 7.94/8.15         (~ (l1_pre_topc @ X0)
% 7.94/8.15          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 7.94/8.15      inference('demod', [status(thm)], ['9', '10'])).
% 7.94/8.15  thf(t24_yellow_1, conjecture,
% 7.94/8.15    (![A:$i]:
% 7.94/8.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.94/8.15       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 7.94/8.15         ( u1_struct_0 @ A ) ) ))).
% 7.94/8.15  thf(zf_stmt_0, negated_conjecture,
% 7.94/8.15    (~( ![A:$i]:
% 7.94/8.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 7.94/8.15            ( l1_pre_topc @ A ) ) =>
% 7.94/8.15          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 7.94/8.15            ( u1_struct_0 @ A ) ) ) )),
% 7.94/8.15    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 7.94/8.15  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf(d1_pre_topc, axiom,
% 7.94/8.15    (![A:$i]:
% 7.94/8.15     ( ( l1_pre_topc @ A ) =>
% 7.94/8.15       ( ( v2_pre_topc @ A ) <=>
% 7.94/8.15         ( ( ![B:$i]:
% 7.94/8.15             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.94/8.15               ( ![C:$i]:
% 7.94/8.15                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.94/8.15                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 7.94/8.15                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 7.94/8.15                     ( r2_hidden @
% 7.94/8.15                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 7.94/8.15                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 7.94/8.15           ( ![B:$i]:
% 7.94/8.15             ( ( m1_subset_1 @
% 7.94/8.15                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.94/8.15               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 7.94/8.15                 ( r2_hidden @
% 7.94/8.15                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 7.94/8.15                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 7.94/8.15           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 7.94/8.15  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 7.94/8.15  thf(zf_stmt_2, axiom,
% 7.94/8.15    (![B:$i,A:$i]:
% 7.94/8.15     ( ( zip_tseitin_5 @ B @ A ) <=>
% 7.94/8.15       ( ( m1_subset_1 @
% 7.94/8.15           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.94/8.15         ( zip_tseitin_4 @ B @ A ) ) ))).
% 7.94/8.15  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 7.94/8.15  thf(zf_stmt_4, axiom,
% 7.94/8.15    (![B:$i,A:$i]:
% 7.94/8.15     ( ( zip_tseitin_4 @ B @ A ) <=>
% 7.94/8.15       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 7.94/8.15         ( r2_hidden @
% 7.94/8.15           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 7.94/8.15  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 7.94/8.15  thf(zf_stmt_6, axiom,
% 7.94/8.15    (![B:$i,A:$i]:
% 7.94/8.15     ( ( zip_tseitin_3 @ B @ A ) <=>
% 7.94/8.15       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.94/8.15         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 7.94/8.15  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 7.94/8.15  thf(zf_stmt_8, axiom,
% 7.94/8.15    (![C:$i,B:$i,A:$i]:
% 7.94/8.15     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 7.94/8.15       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.94/8.15         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 7.94/8.15  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.94/8.15  thf(zf_stmt_10, axiom,
% 7.94/8.15    (![C:$i,B:$i,A:$i]:
% 7.94/8.15     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 7.94/8.15       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 7.94/8.15         ( r2_hidden @
% 7.94/8.15           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 7.94/8.15  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 7.94/8.15  thf(zf_stmt_12, axiom,
% 7.94/8.15    (![C:$i,B:$i,A:$i]:
% 7.94/8.15     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 7.94/8.15       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 7.94/8.15         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 7.94/8.15  thf(zf_stmt_13, axiom,
% 7.94/8.15    (![A:$i]:
% 7.94/8.15     ( ( l1_pre_topc @ A ) =>
% 7.94/8.15       ( ( v2_pre_topc @ A ) <=>
% 7.94/8.15         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 7.94/8.15           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 7.94/8.15           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 7.94/8.15  thf('13', plain,
% 7.94/8.15      (![X40 : $i, X42 : $i]:
% 7.94/8.15         (~ (v2_pre_topc @ X40)
% 7.94/8.15          | (zip_tseitin_5 @ X42 @ X40)
% 7.94/8.15          | ~ (l1_pre_topc @ X40))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_13])).
% 7.94/8.15  thf('14', plain,
% 7.94/8.15      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 7.94/8.15      inference('sup-', [status(thm)], ['12', '13'])).
% 7.94/8.15  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf('16', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 7.94/8.15      inference('demod', [status(thm)], ['14', '15'])).
% 7.94/8.15  thf('17', plain,
% 7.94/8.15      (![X43 : $i]:
% 7.94/8.15         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 7.94/8.15           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 7.94/8.15          | ~ (l1_pre_topc @ X43))),
% 7.94/8.15      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 7.94/8.15  thf('18', plain,
% 7.94/8.15      (![X37 : $i, X38 : $i]:
% 7.94/8.15         (~ (m1_subset_1 @ X37 @ 
% 7.94/8.15             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38))))
% 7.94/8.15          | (zip_tseitin_4 @ X37 @ X38)
% 7.94/8.15          | ~ (zip_tseitin_5 @ X37 @ X38))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.94/8.15  thf('19', plain,
% 7.94/8.15      (![X0 : $i]:
% 7.94/8.15         (~ (l1_pre_topc @ X0)
% 7.94/8.15          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 7.94/8.15          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 7.94/8.15      inference('sup-', [status(thm)], ['17', '18'])).
% 7.94/8.15  thf('20', plain,
% 7.94/8.15      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 7.94/8.15      inference('sup-', [status(thm)], ['16', '19'])).
% 7.94/8.15  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf('22', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 7.94/8.15      inference('demod', [status(thm)], ['20', '21'])).
% 7.94/8.15  thf(d10_xboole_0, axiom,
% 7.94/8.15    (![A:$i,B:$i]:
% 7.94/8.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.94/8.15  thf('23', plain,
% 7.94/8.15      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 7.94/8.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.94/8.15  thf('24', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 7.94/8.15      inference('simplify', [status(thm)], ['23'])).
% 7.94/8.15  thf('25', plain,
% 7.94/8.15      (![X34 : $i, X35 : $i]:
% 7.94/8.15         (~ (r1_tarski @ X34 @ (u1_pre_topc @ X35))
% 7.94/8.15          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X35) @ X34) @ 
% 7.94/8.15             (u1_pre_topc @ X35))
% 7.94/8.15          | ~ (zip_tseitin_4 @ X34 @ X35))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_4])).
% 7.94/8.15  thf('26', plain,
% 7.94/8.15      (![X0 : $i]:
% 7.94/8.15         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 7.94/8.15          | (r2_hidden @ 
% 7.94/8.15             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 7.94/8.15             (u1_pre_topc @ X0)))),
% 7.94/8.15      inference('sup-', [status(thm)], ['24', '25'])).
% 7.94/8.15  thf('27', plain,
% 7.94/8.15      ((r2_hidden @ 
% 7.94/8.15        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 7.94/8.15        (u1_pre_topc @ sk_A))),
% 7.94/8.15      inference('sup-', [status(thm)], ['22', '26'])).
% 7.94/8.15  thf('28', plain,
% 7.94/8.15      (![X40 : $i]:
% 7.94/8.15         (~ (v2_pre_topc @ X40)
% 7.94/8.15          | (r2_hidden @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40))
% 7.94/8.15          | ~ (l1_pre_topc @ X40))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_13])).
% 7.94/8.15  thf('29', plain,
% 7.94/8.15      (![X18 : $i, X20 : $i, X21 : $i]:
% 7.94/8.15         ((zip_tseitin_0 @ X20 @ X18 @ X21)
% 7.94/8.15          | ~ (r2_hidden @ X20 @ (u1_pre_topc @ X21))
% 7.94/8.15          | ~ (r2_hidden @ X18 @ (u1_pre_topc @ X21)))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_12])).
% 7.94/8.15  thf('30', plain,
% 7.94/8.15      (![X0 : $i, X1 : $i]:
% 7.94/8.15         (~ (l1_pre_topc @ X0)
% 7.94/8.15          | ~ (v2_pre_topc @ X0)
% 7.94/8.15          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 7.94/8.15          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 7.94/8.15      inference('sup-', [status(thm)], ['28', '29'])).
% 7.94/8.15  thf('31', plain,
% 7.94/8.15      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.94/8.15         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 7.94/8.15        | ~ (v2_pre_topc @ sk_A)
% 7.94/8.15        | ~ (l1_pre_topc @ sk_A))),
% 7.94/8.15      inference('sup-', [status(thm)], ['27', '30'])).
% 7.94/8.15  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf('34', plain,
% 7.94/8.15      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 7.94/8.15        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 7.94/8.15      inference('demod', [status(thm)], ['31', '32', '33'])).
% 7.94/8.15  thf('35', plain,
% 7.94/8.15      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.94/8.15         ((r2_hidden @ X20 @ (u1_pre_topc @ X19))
% 7.94/8.15          | ~ (zip_tseitin_0 @ X20 @ X18 @ X19))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_12])).
% 7.94/8.15  thf('36', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 7.94/8.15      inference('sup-', [status(thm)], ['34', '35'])).
% 7.94/8.15  thf(l49_zfmisc_1, axiom,
% 7.94/8.15    (![A:$i,B:$i]:
% 7.94/8.15     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 7.94/8.15  thf('37', plain,
% 7.94/8.15      (![X10 : $i, X11 : $i]:
% 7.94/8.15         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 7.94/8.15      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 7.94/8.15  thf('38', plain,
% 7.94/8.15      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 7.94/8.15      inference('sup-', [status(thm)], ['36', '37'])).
% 7.94/8.15  thf('39', plain,
% 7.94/8.15      (![X7 : $i, X9 : $i]:
% 7.94/8.15         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 7.94/8.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.94/8.15  thf('40', plain,
% 7.94/8.15      ((~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 7.94/8.15           (u1_struct_0 @ sk_A))
% 7.94/8.15        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 7.94/8.15      inference('sup-', [status(thm)], ['38', '39'])).
% 7.94/8.15  thf('41', plain,
% 7.94/8.15      ((~ (l1_pre_topc @ sk_A)
% 7.94/8.15        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 7.94/8.15      inference('sup-', [status(thm)], ['11', '40'])).
% 7.94/8.15  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf('43', plain,
% 7.94/8.15      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 7.94/8.15      inference('demod', [status(thm)], ['41', '42'])).
% 7.94/8.15  thf(t14_yellow_1, axiom,
% 7.94/8.15    (![A:$i]:
% 7.94/8.15     ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.94/8.15       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 7.94/8.15         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 7.94/8.15  thf('44', plain,
% 7.94/8.15      (![X44 : $i]:
% 7.94/8.15         (~ (r2_hidden @ (k3_tarski @ X44) @ X44)
% 7.94/8.15          | ((k4_yellow_0 @ (k2_yellow_1 @ X44)) = (k3_tarski @ X44))
% 7.94/8.15          | (v1_xboole_0 @ X44))),
% 7.94/8.15      inference('cnf', [status(esa)], [t14_yellow_1])).
% 7.94/8.15  thf(d1_xboole_0, axiom,
% 7.94/8.15    (![A:$i]:
% 7.94/8.15     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 7.94/8.15  thf('45', plain,
% 7.94/8.15      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.94/8.15      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.94/8.15  thf('46', plain,
% 7.94/8.15      (![X44 : $i]:
% 7.94/8.15         (((k4_yellow_0 @ (k2_yellow_1 @ X44)) = (k3_tarski @ X44))
% 7.94/8.15          | ~ (r2_hidden @ (k3_tarski @ X44) @ X44))),
% 7.94/8.15      inference('clc', [status(thm)], ['44', '45'])).
% 7.94/8.15  thf('47', plain,
% 7.94/8.15      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.94/8.15        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 7.94/8.15            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 7.94/8.15      inference('sup-', [status(thm)], ['43', '46'])).
% 7.94/8.15  thf('48', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 7.94/8.15      inference('sup-', [status(thm)], ['34', '35'])).
% 7.94/8.15  thf('49', plain,
% 7.94/8.15      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 7.94/8.15      inference('demod', [status(thm)], ['41', '42'])).
% 7.94/8.15  thf('50', plain,
% 7.94/8.15      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 7.94/8.15         = (u1_struct_0 @ sk_A))),
% 7.94/8.15      inference('demod', [status(thm)], ['47', '48', '49'])).
% 7.94/8.15  thf('51', plain,
% 7.94/8.15      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 7.94/8.15         != (u1_struct_0 @ sk_A))),
% 7.94/8.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.94/8.15  thf('52', plain, ($false),
% 7.94/8.15      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 7.94/8.15  
% 7.94/8.15  % SZS output end Refutation
% 7.94/8.15  
% 7.94/8.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
