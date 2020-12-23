%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HvFMERNrOT

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 155 expanded)
%              Number of leaves         :   47 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  691 (1235 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X42 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ ( k3_tarski @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X37: $i] :
      ( ~ ( v2_pre_topc @ X37 )
      | ( r2_hidden @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X37: $i] :
      ( ~ ( v2_pre_topc @ X37 )
      | ( r2_hidden @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( r2_hidden @ X40 @ ( u1_pre_topc @ X41 ) )
      | ( v3_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v3_pre_topc @ X40 @ X41 )
      | ( r2_hidden @ X40 @ ( u1_pre_topc @ X41 ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('32',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X47 ) @ X47 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X47 ) )
        = ( k3_tarski @ X47 ) )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('34',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('35',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('42',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf(fc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('44',plain,(
    ! [X43: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ X43 ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc1_pre_topc])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HvFMERNrOT
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:53:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 210 iterations in 0.117s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.21/0.57  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.21/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.57  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(dt_u1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( m1_subset_1 @
% 0.21/0.57         ( u1_pre_topc @ A ) @ 
% 0.21/0.57         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X42 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (u1_pre_topc @ X42) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42))))
% 0.21/0.57          | ~ (l1_pre_topc @ X42))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i]:
% 0.21/0.57         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf(t95_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.57       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]:
% 0.21/0.57         ((r1_tarski @ (k3_tarski @ X5) @ (k3_tarski @ X6))
% 0.21/0.57          | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.21/0.57             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf(t99_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.57  thf('5', plain, (![X7 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X7)) = (X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf(d1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ( v2_pre_topc @ A ) <=>
% 0.21/0.57         ( ( ![B:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57               ( ![C:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.57                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.57                     ( r2_hidden @
% 0.21/0.57                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.21/0.57                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.21/0.57           ( ![B:$i]:
% 0.21/0.57             ( ( m1_subset_1 @
% 0.21/0.57                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.57               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.21/0.57                 ( r2_hidden @
% 0.21/0.57                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.57                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.21/0.57           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_1, axiom,
% 0.21/0.57    (![B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.21/0.57       ( ( m1_subset_1 @
% 0.21/0.57           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.57         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.21/0.57  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_3, axiom,
% 0.21/0.57    (![B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.21/0.57       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.21/0.57         ( r2_hidden @
% 0.21/0.57           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_5, axiom,
% 0.21/0.57    (![B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.21/0.57       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_7, axiom,
% 0.21/0.57    (![C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.21/0.57       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.21/0.57  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_9, axiom,
% 0.21/0.57    (![C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.21/0.57       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.57         ( r2_hidden @
% 0.21/0.57           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_11, axiom,
% 0.21/0.57    (![C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.21/0.57       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.57         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_12, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ( v2_pre_topc @ A ) <=>
% 0.21/0.57         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.57           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.21/0.57           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X37 : $i]:
% 0.21/0.57         (~ (v2_pre_topc @ X37)
% 0.21/0.57          | (r2_hidden @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 0.21/0.57          | ~ (l1_pre_topc @ X37))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.21/0.57  thf(l49_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i, X2 : $i]:
% 0.21/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.21/0.57               (u1_struct_0 @ X0))
% 0.21/0.57          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v2_pre_topc @ X0)
% 0.21/0.57          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X37 : $i]:
% 0.21/0.57         (~ (v2_pre_topc @ X37)
% 0.21/0.57          | (r2_hidden @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37))
% 0.21/0.57          | ~ (l1_pre_topc @ X37))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v2_pre_topc @ X0)
% 0.21/0.57          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X12 : $i, X14 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf(d5_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.57             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X40 : $i, X41 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.57          | ~ (r2_hidden @ X40 @ (u1_pre_topc @ X41))
% 0.21/0.57          | (v3_pre_topc @ X40 @ X41)
% 0.21/0.57          | ~ (l1_pre_topc @ X41))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0)
% 0.21/0.57          | ~ (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.21/0.57               (u1_pre_topc @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 0.21/0.57          | (v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | (v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X40 : $i, X41 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.57          | ~ (v3_pre_topc @ X40 @ X41)
% 0.21/0.57          | (r2_hidden @ X40 @ (u1_pre_topc @ X41))
% 0.21/0.57          | ~ (l1_pre_topc @ X41))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 0.21/0.57          | ~ (v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v3_pre_topc @ (k3_tarski @ (u1_pre_topc @ X0)) @ X0)
% 0.21/0.57          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['25', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.57  thf(t14_yellow_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.57       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.57         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X47 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k3_tarski @ X47) @ X47)
% 0.21/0.57          | ((k4_yellow_0 @ (k2_yellow_1 @ X47)) = (k3_tarski @ X47))
% 0.21/0.57          | (v1_xboole_0 @ X47))),
% 0.21/0.57      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.21/0.57          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.21/0.57              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf(t24_yellow_1, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.57         ( u1_struct_0 @ A ) ) ))).
% 0.21/0.57  thf(zf_stmt_13, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57            ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.57            ( u1_struct_0 @ A ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         != (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.21/0.57        | (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.57  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.21/0.57        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '38'])).
% 0.21/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.57        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.57  thf('43', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 0.21/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.57  thf(fc1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ~( v1_xboole_0 @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (![X43 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ (u1_pre_topc @ X43))
% 0.21/0.57          | ~ (l1_pre_topc @ X43)
% 0.21/0.57          | ~ (v2_pre_topc @ X43))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_pre_topc])).
% 0.21/0.57  thf('45', plain, ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.57  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.57  thf('48', plain, ($false),
% 0.21/0.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
