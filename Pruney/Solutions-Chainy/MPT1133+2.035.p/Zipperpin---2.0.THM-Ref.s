%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tvDUe0xw9O

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:31 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  253 (1513 expanded)
%              Number of leaves         :   51 ( 457 expanded)
%              Depth                    :   34
%              Number of atoms          : 3492 (35161 expanded)
%              Number of equality atoms :   29 ( 471 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X35 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('4',plain,(
    ! [X36: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ( r2_hidden @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r2_hidden @ X31 @ ( u1_pre_topc @ X32 ) )
      | ( v3_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_pre_topc @ X37 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t64_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_pre_topc])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t62_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v5_pre_topc @ X43 @ X42 @ X40 )
      | ( v5_pre_topc @ X41 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) @ X40 )
      | ( X43 != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('41',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( v5_pre_topc @ X41 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) @ X40 )
      | ~ ( v5_pre_topc @ X41 @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('45',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('46',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','47','48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('52',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('53',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('56',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('60',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('62',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(t63_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X47 @ X46 @ X44 )
      | ( v5_pre_topc @ X45 @ X46 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) )
      | ( X47 != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('70',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ( v5_pre_topc @ X45 @ X46 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) )
      | ~ ( v5_pre_topc @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('73',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('74',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('75',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('77',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('80',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['62','80'])).

thf('82',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('83',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('84',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('87',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('89',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('92',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('93',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('96',plain,(
    ! [X36: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('97',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['61'])).

thf('98',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('99',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('101',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X45 @ X46 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) )
      | ( v5_pre_topc @ X47 @ X46 @ X44 )
      | ( X47 != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('102',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ( v5_pre_topc @ X45 @ X46 @ X44 )
      | ~ ( v5_pre_topc @ X45 @ X46 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('105',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('106',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('107',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('108',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('111',plain,(
    ! [X28: $i,X30: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ( zip_tseitin_5 @ X30 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X35 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('116',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) )
      | ( zip_tseitin_4 @ X25 @ X26 )
      | ~ ( zip_tseitin_5 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('120',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('122',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( u1_pre_topc @ X23 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ ( u1_pre_topc @ X23 ) )
      | ~ ( zip_tseitin_4 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ( r2_hidden @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('126',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X8 @ X6 @ X9 )
      | ~ ( r2_hidden @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( r2_hidden @ X6 @ ( u1_pre_topc @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('131',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( u1_pre_topc @ X7 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('133',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('135',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('137',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('142',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('144',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('146',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('150',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('152',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('153',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('154',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','150','151','152','153'])).

thf('155',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['99','154'])).

thf('156',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['96','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('159',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['95','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('162',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('166',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v5_pre_topc @ X41 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) @ X40 )
      | ( v5_pre_topc @ X43 @ X42 @ X40 )
      | ( X43 != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('167',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( v5_pre_topc @ X41 @ X42 @ X40 )
      | ~ ( v5_pre_topc @ X41 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['163','171'])).

thf('173',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('175',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('176',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('177',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('178',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('179',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['172','173','174','175','176','177','178'])).

thf('180',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['162','179'])).

thf('181',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['86'])).

thf('182',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('184',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['90','94','182','183'])).

thf('185',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['81','184'])).

thf('186',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['54','60','185'])).

thf('187',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('188',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('189',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
   <= ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['93'])).

thf('190',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['90','94','182','190'])).

thf('192',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(simpl_trail,[status(thm)],['187','191'])).

thf('193',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['186','192'])).

thf('194',plain,
    ( ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['3','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('196',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('197',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['198','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tvDUe0xw9O
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.73/2.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.73/2.98  % Solved by: fo/fo7.sh
% 2.73/2.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.98  % done 2349 iterations in 2.518s
% 2.73/2.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.73/2.98  % SZS output start Refutation
% 2.73/2.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.73/2.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.73/2.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.73/2.98  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 2.73/2.98  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 2.73/2.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.73/2.98  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.73/2.98  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.73/2.98  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.98  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 2.73/2.98  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 2.73/2.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.98  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 2.73/2.98  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.73/2.98  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 2.73/2.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.73/2.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.73/2.98  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 2.73/2.98  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.73/2.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 2.73/2.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.73/2.98  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 2.73/2.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.73/2.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.73/2.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.73/2.98  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.73/2.98  thf(dt_u1_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( l1_pre_topc @ A ) =>
% 2.73/2.98       ( m1_subset_1 @
% 2.73/2.98         ( u1_pre_topc @ A ) @ 
% 2.73/2.98         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 2.73/2.98  thf('0', plain,
% 2.73/2.98      (![X35 : $i]:
% 2.73/2.98         ((m1_subset_1 @ (u1_pre_topc @ X35) @ 
% 2.73/2.98           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))
% 2.73/2.98          | ~ (l1_pre_topc @ X35))),
% 2.73/2.98      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 2.73/2.98  thf(dt_g1_pre_topc, axiom,
% 2.73/2.98    (![A:$i,B:$i]:
% 2.73/2.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.73/2.98       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 2.73/2.98         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 2.73/2.98  thf('1', plain,
% 2.73/2.98      (![X33 : $i, X34 : $i]:
% 2.73/2.98         ((l1_pre_topc @ (g1_pre_topc @ X33 @ X34))
% 2.73/2.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X33))))),
% 2.73/2.98      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 2.73/2.98  thf('2', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['0', '1'])).
% 2.73/2.98  thf(fc6_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.73/2.98       ( ( v1_pre_topc @
% 2.73/2.98           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 2.73/2.98         ( v2_pre_topc @
% 2.73/2.98           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 2.73/2.98  thf('3', plain,
% 2.73/2.98      (![X36 : $i]:
% 2.73/2.98         ((v2_pre_topc @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 2.73/2.98          | ~ (l1_pre_topc @ X36)
% 2.73/2.98          | ~ (v2_pre_topc @ X36))),
% 2.73/2.98      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 2.73/2.98  thf('4', plain,
% 2.73/2.98      (![X36 : $i]:
% 2.73/2.98         ((v2_pre_topc @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 2.73/2.98          | ~ (l1_pre_topc @ X36)
% 2.73/2.98          | ~ (v2_pre_topc @ X36))),
% 2.73/2.98      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 2.73/2.98  thf('5', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['0', '1'])).
% 2.73/2.98  thf(d1_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( l1_pre_topc @ A ) =>
% 2.73/2.98       ( ( v2_pre_topc @ A ) <=>
% 2.73/2.98         ( ( ![B:$i]:
% 2.73/2.98             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.73/2.98               ( ![C:$i]:
% 2.73/2.98                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.73/2.98                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 2.73/2.98                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 2.73/2.98                     ( r2_hidden @
% 2.73/2.98                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 2.73/2.98                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 2.73/2.98           ( ![B:$i]:
% 2.73/2.98             ( ( m1_subset_1 @
% 2.73/2.98                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.73/2.98               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.73/2.98                 ( r2_hidden @
% 2.73/2.98                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 2.73/2.98                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 2.73/2.98           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 2.73/2.98  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 2.73/2.98  thf(zf_stmt_1, axiom,
% 2.73/2.98    (![B:$i,A:$i]:
% 2.73/2.98     ( ( zip_tseitin_5 @ B @ A ) <=>
% 2.73/2.98       ( ( m1_subset_1 @
% 2.73/2.98           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.73/2.98         ( zip_tseitin_4 @ B @ A ) ) ))).
% 2.73/2.98  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 2.73/2.98  thf(zf_stmt_3, axiom,
% 2.73/2.98    (![B:$i,A:$i]:
% 2.73/2.98     ( ( zip_tseitin_4 @ B @ A ) <=>
% 2.73/2.98       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.73/2.98         ( r2_hidden @
% 2.73/2.98           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.73/2.98  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 2.73/2.98  thf(zf_stmt_5, axiom,
% 2.73/2.98    (![B:$i,A:$i]:
% 2.73/2.98     ( ( zip_tseitin_3 @ B @ A ) <=>
% 2.73/2.98       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.73/2.98         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 2.73/2.98  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 2.73/2.98  thf(zf_stmt_7, axiom,
% 2.73/2.98    (![C:$i,B:$i,A:$i]:
% 2.73/2.98     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 2.73/2.98       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.73/2.98         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 2.73/2.98  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.73/2.98  thf(zf_stmt_9, axiom,
% 2.73/2.98    (![C:$i,B:$i,A:$i]:
% 2.73/2.98     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 2.73/2.98       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 2.73/2.98         ( r2_hidden @
% 2.73/2.98           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.73/2.98  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 2.73/2.98  thf(zf_stmt_11, axiom,
% 2.73/2.98    (![C:$i,B:$i,A:$i]:
% 2.73/2.98     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 2.73/2.98       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 2.73/2.98         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 2.73/2.98  thf(zf_stmt_12, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( l1_pre_topc @ A ) =>
% 2.73/2.98       ( ( v2_pre_topc @ A ) <=>
% 2.73/2.98         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 2.73/2.98           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 2.73/2.98           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 2.73/2.98  thf('6', plain,
% 2.73/2.98      (![X28 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X28)
% 2.73/2.98          | (r2_hidden @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28))
% 2.73/2.98          | ~ (l1_pre_topc @ X28))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.73/2.98  thf(d10_xboole_0, axiom,
% 2.73/2.98    (![A:$i,B:$i]:
% 2.73/2.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.73/2.98  thf('7', plain,
% 2.73/2.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.73/2.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.73/2.98  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.73/2.98      inference('simplify', [status(thm)], ['7'])).
% 2.73/2.98  thf(t3_subset, axiom,
% 2.73/2.98    (![A:$i,B:$i]:
% 2.73/2.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.73/2.98  thf('9', plain,
% 2.73/2.98      (![X3 : $i, X5 : $i]:
% 2.73/2.98         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 2.73/2.98      inference('cnf', [status(esa)], [t3_subset])).
% 2.73/2.98  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['8', '9'])).
% 2.73/2.98  thf(d5_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( l1_pre_topc @ A ) =>
% 2.73/2.98       ( ![B:$i]:
% 2.73/2.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.73/2.98           ( ( v3_pre_topc @ B @ A ) <=>
% 2.73/2.98             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 2.73/2.98  thf('11', plain,
% 2.73/2.98      (![X31 : $i, X32 : $i]:
% 2.73/2.98         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 2.73/2.98          | ~ (r2_hidden @ X31 @ (u1_pre_topc @ X32))
% 2.73/2.98          | (v3_pre_topc @ X31 @ X32)
% 2.73/2.98          | ~ (l1_pre_topc @ X32))),
% 2.73/2.98      inference('cnf', [status(esa)], [d5_pre_topc])).
% 2.73/2.98  thf('12', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.73/2.98          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 2.73/2.98      inference('sup-', [status(thm)], ['10', '11'])).
% 2.73/2.98  thf('13', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['6', '12'])).
% 2.73/2.98  thf('14', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['13'])).
% 2.73/2.98  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['8', '9'])).
% 2.73/2.98  thf(t60_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.73/2.98       ( ![B:$i]:
% 2.73/2.98         ( ( ( v3_pre_topc @ B @ A ) & 
% 2.73/2.98             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 2.73/2.98           ( ( v3_pre_topc @
% 2.73/2.98               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 2.73/2.98             ( m1_subset_1 @
% 2.73/2.98               B @ 
% 2.73/2.98               ( k1_zfmisc_1 @
% 2.73/2.98                 ( u1_struct_0 @
% 2.73/2.98                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 2.73/2.98  thf('16', plain,
% 2.73/2.98      (![X37 : $i, X38 : $i]:
% 2.73/2.98         (~ (v3_pre_topc @ X37 @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 2.73/2.98          | ~ (m1_subset_1 @ X37 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (u1_struct_0 @ 
% 2.73/2.98                 (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))))
% 2.73/2.98          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 2.73/2.98          | ~ (l1_pre_topc @ X38)
% 2.73/2.98          | ~ (v2_pre_topc @ X38))),
% 2.73/2.98      inference('cnf', [status(esa)], [t60_pre_topc])).
% 2.73/2.98  thf('17', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | (m1_subset_1 @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.73/2.98          | ~ (v3_pre_topc @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['15', '16'])).
% 2.73/2.98  thf('18', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98          | ~ (v2_pre_topc @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98          | (m1_subset_1 @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['14', '17'])).
% 2.73/2.98  thf('19', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | (m1_subset_1 @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.73/2.98          | ~ (v2_pre_topc @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['5', '18'])).
% 2.73/2.98  thf('20', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98          | (m1_subset_1 @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['19'])).
% 2.73/2.98  thf('21', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | (m1_subset_1 @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['4', '20'])).
% 2.73/2.98  thf('22', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         ((m1_subset_1 @ 
% 2.73/2.98           (u1_struct_0 @ 
% 2.73/2.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['21'])).
% 2.73/2.98  thf('23', plain,
% 2.73/2.98      (![X3 : $i, X4 : $i]:
% 2.73/2.98         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.73/2.98      inference('cnf', [status(esa)], [t3_subset])).
% 2.73/2.98  thf('24', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | (r1_tarski @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98             (u1_struct_0 @ X0)))),
% 2.73/2.98      inference('sup-', [status(thm)], ['22', '23'])).
% 2.73/2.98  thf('25', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['13'])).
% 2.73/2.98  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['8', '9'])).
% 2.73/2.98  thf('27', plain,
% 2.73/2.98      (![X38 : $i, X39 : $i]:
% 2.73/2.98         (~ (v3_pre_topc @ X39 @ X38)
% 2.73/2.98          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 2.73/2.98          | (m1_subset_1 @ X39 @ 
% 2.73/2.98             (k1_zfmisc_1 @ 
% 2.73/2.98              (u1_struct_0 @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))))
% 2.73/2.98          | ~ (l1_pre_topc @ X38)
% 2.73/2.98          | ~ (v2_pre_topc @ X38))),
% 2.73/2.98      inference('cnf', [status(esa)], [t60_pre_topc])).
% 2.73/2.98  thf('28', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.73/2.98             (k1_zfmisc_1 @ 
% 2.73/2.98              (u1_struct_0 @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 2.73/2.98          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['26', '27'])).
% 2.73/2.98  thf('29', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.73/2.98             (k1_zfmisc_1 @ 
% 2.73/2.98              (u1_struct_0 @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['25', '28'])).
% 2.73/2.98  thf('30', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.73/2.98           (k1_zfmisc_1 @ 
% 2.73/2.98            (u1_struct_0 @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['29'])).
% 2.73/2.98  thf('31', plain,
% 2.73/2.98      (![X3 : $i, X4 : $i]:
% 2.73/2.98         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.73/2.98      inference('cnf', [status(esa)], [t3_subset])).
% 2.73/2.98  thf('32', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['30', '31'])).
% 2.73/2.98  thf('33', plain,
% 2.73/2.98      (![X0 : $i, X2 : $i]:
% 2.73/2.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.73/2.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.73/2.98  thf('34', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (r1_tarski @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.98               (u1_struct_0 @ X0))
% 2.73/2.98          | ((u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98              = (u1_struct_0 @ X0)))),
% 2.73/2.98      inference('sup-', [status(thm)], ['32', '33'])).
% 2.73/2.98  thf('35', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ((u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98              = (u1_struct_0 @ X0))
% 2.73/2.98          | ~ (l1_pre_topc @ X0)
% 2.73/2.98          | ~ (v2_pre_topc @ X0))),
% 2.73/2.98      inference('sup-', [status(thm)], ['24', '34'])).
% 2.73/2.98  thf('36', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (((u1_struct_0 @ 
% 2.73/2.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98            = (u1_struct_0 @ X0))
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['35'])).
% 2.73/2.98  thf(t64_pre_topc, conjecture,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.73/2.98       ( ![B:$i]:
% 2.73/2.98         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 2.73/2.98           ( ![C:$i]:
% 2.73/2.98             ( ( ( v1_funct_1 @ C ) & 
% 2.73/2.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.73/2.98                 ( m1_subset_1 @
% 2.73/2.98                   C @ 
% 2.73/2.98                   ( k1_zfmisc_1 @
% 2.73/2.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.73/2.98               ( ![D:$i]:
% 2.73/2.98                 ( ( ( v1_funct_1 @ D ) & 
% 2.73/2.98                     ( v1_funct_2 @
% 2.73/2.98                       D @ 
% 2.73/2.98                       ( u1_struct_0 @
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 2.73/2.98                       ( u1_struct_0 @
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 2.73/2.98                     ( m1_subset_1 @
% 2.73/2.98                       D @ 
% 2.73/2.98                       ( k1_zfmisc_1 @
% 2.73/2.98                         ( k2_zfmisc_1 @
% 2.73/2.98                           ( u1_struct_0 @
% 2.73/2.98                             ( g1_pre_topc @
% 2.73/2.98                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 2.73/2.98                           ( u1_struct_0 @
% 2.73/2.98                             ( g1_pre_topc @
% 2.73/2.98                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 2.73/2.98                   ( ( ( C ) = ( D ) ) =>
% 2.73/2.98                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 2.73/2.98                       ( v5_pre_topc @
% 2.73/2.98                         D @ 
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.73/2.98  thf(zf_stmt_13, negated_conjecture,
% 2.73/2.98    (~( ![A:$i]:
% 2.73/2.98        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.73/2.98          ( ![B:$i]:
% 2.73/2.98            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 2.73/2.98              ( ![C:$i]:
% 2.73/2.98                ( ( ( v1_funct_1 @ C ) & 
% 2.73/2.98                    ( v1_funct_2 @
% 2.73/2.98                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.73/2.98                    ( m1_subset_1 @
% 2.73/2.98                      C @ 
% 2.73/2.98                      ( k1_zfmisc_1 @
% 2.73/2.98                        ( k2_zfmisc_1 @
% 2.73/2.98                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.73/2.98                  ( ![D:$i]:
% 2.73/2.98                    ( ( ( v1_funct_1 @ D ) & 
% 2.73/2.98                        ( v1_funct_2 @
% 2.73/2.98                          D @ 
% 2.73/2.98                          ( u1_struct_0 @
% 2.73/2.98                            ( g1_pre_topc @
% 2.73/2.98                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 2.73/2.98                          ( u1_struct_0 @
% 2.73/2.98                            ( g1_pre_topc @
% 2.73/2.98                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 2.73/2.98                        ( m1_subset_1 @
% 2.73/2.98                          D @ 
% 2.73/2.98                          ( k1_zfmisc_1 @
% 2.73/2.98                            ( k2_zfmisc_1 @
% 2.73/2.98                              ( u1_struct_0 @
% 2.73/2.98                                ( g1_pre_topc @
% 2.73/2.98                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 2.73/2.98                              ( u1_struct_0 @
% 2.73/2.98                                ( g1_pre_topc @
% 2.73/2.98                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 2.73/2.98                      ( ( ( C ) = ( D ) ) =>
% 2.73/2.98                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 2.73/2.98                          ( v5_pre_topc @
% 2.73/2.98                            D @ 
% 2.73/2.98                            ( g1_pre_topc @
% 2.73/2.98                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 2.73/2.98                            ( g1_pre_topc @
% 2.73/2.98                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.73/2.98    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 2.73/2.98  thf('37', plain,
% 2.73/2.98      ((m1_subset_1 @ sk_D @ 
% 2.73/2.98        (k1_zfmisc_1 @ 
% 2.73/2.98         (k2_zfmisc_1 @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('38', plain, (((sk_C_1) = (sk_D))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('39', plain,
% 2.73/2.98      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98        (k1_zfmisc_1 @ 
% 2.73/2.98         (k2_zfmisc_1 @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))),
% 2.73/2.98      inference('demod', [status(thm)], ['37', '38'])).
% 2.73/2.98  thf(t62_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.73/2.98       ( ![B:$i]:
% 2.73/2.98         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 2.73/2.98           ( ![C:$i]:
% 2.73/2.98             ( ( ( v1_funct_1 @ C ) & 
% 2.73/2.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.73/2.98                 ( m1_subset_1 @
% 2.73/2.98                   C @ 
% 2.73/2.98                   ( k1_zfmisc_1 @
% 2.73/2.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.73/2.98               ( ![D:$i]:
% 2.73/2.98                 ( ( ( v1_funct_1 @ D ) & 
% 2.73/2.98                     ( v1_funct_2 @
% 2.73/2.98                       D @ 
% 2.73/2.98                       ( u1_struct_0 @
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 2.73/2.98                       ( u1_struct_0 @ B ) ) & 
% 2.73/2.98                     ( m1_subset_1 @
% 2.73/2.98                       D @ 
% 2.73/2.98                       ( k1_zfmisc_1 @
% 2.73/2.98                         ( k2_zfmisc_1 @
% 2.73/2.98                           ( u1_struct_0 @
% 2.73/2.98                             ( g1_pre_topc @
% 2.73/2.98                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 2.73/2.98                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.73/2.98                   ( ( ( C ) = ( D ) ) =>
% 2.73/2.98                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 2.73/2.98                       ( v5_pre_topc @
% 2.73/2.98                         D @ 
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 2.73/2.98                         B ) ) ) ) ) ) ) ) ) ))).
% 2.73/2.98  thf('40', plain,
% 2.73/2.98      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X40)
% 2.73/2.98          | ~ (l1_pre_topc @ X40)
% 2.73/2.98          | ~ (v1_funct_1 @ X41)
% 2.73/2.98          | ~ (v1_funct_2 @ X41 @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.98               (u1_struct_0 @ X40))
% 2.73/2.98          | ~ (m1_subset_1 @ X41 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ 
% 2.73/2.98                 (u1_struct_0 @ 
% 2.73/2.98                  (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.98                 (u1_struct_0 @ X40))))
% 2.73/2.98          | ~ (v5_pre_topc @ X43 @ X42 @ X40)
% 2.73/2.98          | (v5_pre_topc @ X41 @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)) @ X40)
% 2.73/2.98          | ((X43) != (X41))
% 2.73/2.98          | ~ (m1_subset_1 @ X43 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 2.73/2.98          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 2.73/2.98          | ~ (v1_funct_1 @ X43)
% 2.73/2.98          | ~ (l1_pre_topc @ X42)
% 2.73/2.98          | ~ (v2_pre_topc @ X42))),
% 2.73/2.98      inference('cnf', [status(esa)], [t62_pre_topc])).
% 2.73/2.98  thf('41', plain,
% 2.73/2.98      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X42)
% 2.73/2.98          | ~ (l1_pre_topc @ X42)
% 2.73/2.98          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 2.73/2.98          | ~ (m1_subset_1 @ X41 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 2.73/2.98          | (v5_pre_topc @ X41 @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)) @ X40)
% 2.73/2.98          | ~ (v5_pre_topc @ X41 @ X42 @ X40)
% 2.73/2.98          | ~ (m1_subset_1 @ X41 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ 
% 2.73/2.98                 (u1_struct_0 @ 
% 2.73/2.98                  (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.98                 (u1_struct_0 @ X40))))
% 2.73/2.98          | ~ (v1_funct_2 @ X41 @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.98               (u1_struct_0 @ X40))
% 2.73/2.98          | ~ (v1_funct_1 @ X41)
% 2.73/2.98          | ~ (l1_pre_topc @ X40)
% 2.73/2.98          | ~ (v2_pre_topc @ X40))),
% 2.73/2.98      inference('simplify', [status(thm)], ['40'])).
% 2.73/2.98  thf('42', plain,
% 2.73/2.98      ((~ (v2_pre_topc @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v1_funct_1 @ sk_C_1)
% 2.73/2.98        | ~ (v1_funct_2 @ sk_C_1 @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98             (k1_zfmisc_1 @ 
% 2.73/2.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))
% 2.73/2.98        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98        | ~ (l1_pre_topc @ sk_A)
% 2.73/2.98        | ~ (v2_pre_topc @ sk_A))),
% 2.73/2.98      inference('sup-', [status(thm)], ['39', '41'])).
% 2.73/2.98  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('44', plain,
% 2.73/2.98      ((v1_funct_2 @ sk_D @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('45', plain, (((sk_C_1) = (sk_D))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('46', plain,
% 2.73/2.98      ((v1_funct_2 @ sk_C_1 @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('demod', [status(thm)], ['44', '45'])).
% 2.73/2.98  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('49', plain,
% 2.73/2.98      ((~ (v2_pre_topc @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98             (k1_zfmisc_1 @ 
% 2.73/2.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))
% 2.73/2.98        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.98      inference('demod', [status(thm)], ['42', '43', '46', '47', '48'])).
% 2.73/2.98  thf('50', plain,
% 2.73/2.98      ((~ (m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98           (k1_zfmisc_1 @ 
% 2.73/2.98            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 2.73/2.98        | ~ (l1_pre_topc @ sk_B_2)
% 2.73/2.98        | ~ (v2_pre_topc @ sk_B_2)
% 2.73/2.98        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v2_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['36', '49'])).
% 2.73/2.98  thf('51', plain,
% 2.73/2.98      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98        (k1_zfmisc_1 @ 
% 2.73/2.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('52', plain, ((l1_pre_topc @ sk_B_2)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('53', plain, ((v2_pre_topc @ sk_B_2)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('54', plain,
% 2.73/2.98      ((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98           (u1_struct_0 @ 
% 2.73/2.98            (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (l1_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v2_pre_topc @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 2.73/2.98  thf('55', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (((u1_struct_0 @ 
% 2.73/2.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98            = (u1_struct_0 @ X0))
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['35'])).
% 2.73/2.98  thf('56', plain,
% 2.73/2.98      ((v1_funct_2 @ sk_C_1 @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('demod', [status(thm)], ['44', '45'])).
% 2.73/2.98  thf('57', plain,
% 2.73/2.98      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98         (u1_struct_0 @ 
% 2.73/2.98          (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98        | ~ (l1_pre_topc @ sk_A)
% 2.73/2.98        | ~ (v2_pre_topc @ sk_A))),
% 2.73/2.98      inference('sup+', [status(thm)], ['55', '56'])).
% 2.73/2.98  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('60', plain,
% 2.73/2.98      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('demod', [status(thm)], ['57', '58', '59'])).
% 2.73/2.98  thf('61', plain,
% 2.73/2.98      (((v5_pre_topc @ sk_D @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('62', plain,
% 2.73/2.98      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))
% 2.73/2.98         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))),
% 2.73/2.98      inference('split', [status(esa)], ['61'])).
% 2.73/2.98  thf('63', plain,
% 2.73/2.98      (![X0 : $i]:
% 2.73/2.98         (((u1_struct_0 @ 
% 2.73/2.98            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.98            = (u1_struct_0 @ X0))
% 2.73/2.98          | ~ (v2_pre_topc @ X0)
% 2.73/2.98          | ~ (l1_pre_topc @ X0))),
% 2.73/2.98      inference('simplify', [status(thm)], ['35'])).
% 2.73/2.98  thf('64', plain,
% 2.73/2.98      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98        (k1_zfmisc_1 @ 
% 2.73/2.98         (k2_zfmisc_1 @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))),
% 2.73/2.98      inference('demod', [status(thm)], ['37', '38'])).
% 2.73/2.98  thf('65', plain,
% 2.73/2.98      (((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98         (k1_zfmisc_1 @ 
% 2.73/2.98          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98           (u1_struct_0 @ 
% 2.73/2.98            (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))
% 2.73/2.98        | ~ (l1_pre_topc @ sk_A)
% 2.73/2.98        | ~ (v2_pre_topc @ sk_A))),
% 2.73/2.98      inference('sup+', [status(thm)], ['63', '64'])).
% 2.73/2.98  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('68', plain,
% 2.73/2.98      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98        (k1_zfmisc_1 @ 
% 2.73/2.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98          (u1_struct_0 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))),
% 2.73/2.98      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.73/2.98  thf(t63_pre_topc, axiom,
% 2.73/2.98    (![A:$i]:
% 2.73/2.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.73/2.98       ( ![B:$i]:
% 2.73/2.98         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 2.73/2.98           ( ![C:$i]:
% 2.73/2.98             ( ( ( v1_funct_1 @ C ) & 
% 2.73/2.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.73/2.98                 ( m1_subset_1 @
% 2.73/2.98                   C @ 
% 2.73/2.98                   ( k1_zfmisc_1 @
% 2.73/2.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.73/2.98               ( ![D:$i]:
% 2.73/2.98                 ( ( ( v1_funct_1 @ D ) & 
% 2.73/2.98                     ( v1_funct_2 @
% 2.73/2.98                       D @ ( u1_struct_0 @ A ) @ 
% 2.73/2.98                       ( u1_struct_0 @
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 2.73/2.98                     ( m1_subset_1 @
% 2.73/2.98                       D @ 
% 2.73/2.98                       ( k1_zfmisc_1 @
% 2.73/2.98                         ( k2_zfmisc_1 @
% 2.73/2.98                           ( u1_struct_0 @ A ) @ 
% 2.73/2.98                           ( u1_struct_0 @
% 2.73/2.98                             ( g1_pre_topc @
% 2.73/2.98                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 2.73/2.98                   ( ( ( C ) = ( D ) ) =>
% 2.73/2.98                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 2.73/2.98                       ( v5_pre_topc @
% 2.73/2.98                         D @ A @ 
% 2.73/2.98                         ( g1_pre_topc @
% 2.73/2.98                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.73/2.98  thf('69', plain,
% 2.73/2.98      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X44)
% 2.73/2.98          | ~ (l1_pre_topc @ X44)
% 2.73/2.98          | ~ (v1_funct_1 @ X45)
% 2.73/2.98          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X46) @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))
% 2.73/2.98          | ~ (m1_subset_1 @ X45 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ 
% 2.73/2.98                 (u1_struct_0 @ 
% 2.73/2.98                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))))
% 2.73/2.98          | ~ (v5_pre_topc @ X47 @ X46 @ X44)
% 2.73/2.98          | (v5_pre_topc @ X45 @ X46 @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)))
% 2.73/2.98          | ((X47) != (X45))
% 2.73/2.98          | ~ (m1_subset_1 @ X47 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))))
% 2.73/2.98          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))
% 2.73/2.98          | ~ (v1_funct_1 @ X47)
% 2.73/2.98          | ~ (l1_pre_topc @ X46)
% 2.73/2.98          | ~ (v2_pre_topc @ X46))),
% 2.73/2.98      inference('cnf', [status(esa)], [t63_pre_topc])).
% 2.73/2.98  thf('70', plain,
% 2.73/2.98      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.73/2.98         (~ (v2_pre_topc @ X46)
% 2.73/2.98          | ~ (l1_pre_topc @ X46)
% 2.73/2.98          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))
% 2.73/2.98          | ~ (m1_subset_1 @ X45 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))))
% 2.73/2.98          | (v5_pre_topc @ X45 @ X46 @ 
% 2.73/2.98             (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)))
% 2.73/2.98          | ~ (v5_pre_topc @ X45 @ X46 @ X44)
% 2.73/2.98          | ~ (m1_subset_1 @ X45 @ 
% 2.73/2.98               (k1_zfmisc_1 @ 
% 2.73/2.98                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ 
% 2.73/2.98                 (u1_struct_0 @ 
% 2.73/2.98                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))))
% 2.73/2.98          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X46) @ 
% 2.73/2.98               (u1_struct_0 @ 
% 2.73/2.98                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))
% 2.73/2.98          | ~ (v1_funct_1 @ X45)
% 2.73/2.98          | ~ (l1_pre_topc @ X44)
% 2.73/2.98          | ~ (v2_pre_topc @ X44))),
% 2.73/2.98      inference('simplify', [status(thm)], ['69'])).
% 2.73/2.98  thf('71', plain,
% 2.73/2.98      ((~ (v2_pre_topc @ sk_B_2)
% 2.73/2.98        | ~ (l1_pre_topc @ sk_B_2)
% 2.73/2.98        | ~ (v1_funct_1 @ sk_C_1)
% 2.73/2.98        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98             (u1_struct_0 @ 
% 2.73/2.98              (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98             (k1_zfmisc_1 @ 
% 2.73/2.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 2.73/2.98        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98             (u1_struct_0 @ sk_B_2))
% 2.73/2.98        | ~ (l1_pre_topc @ sk_A)
% 2.73/2.98        | ~ (v2_pre_topc @ sk_A))),
% 2.73/2.98      inference('sup-', [status(thm)], ['68', '70'])).
% 2.73/2.98  thf('72', plain, ((v2_pre_topc @ sk_B_2)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('73', plain, ((l1_pre_topc @ sk_B_2)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('74', plain, ((v1_funct_1 @ sk_C_1)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('75', plain,
% 2.73/2.98      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.98        (u1_struct_0 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('demod', [status(thm)], ['57', '58', '59'])).
% 2.73/2.98  thf('76', plain,
% 2.73/2.98      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.98        (k1_zfmisc_1 @ 
% 2.73/2.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('77', plain,
% 2.73/2.98      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('80', plain,
% 2.73/2.98      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('demod', [status(thm)],
% 2.73/2.98                ['71', '72', '73', '74', '75', '76', '77', '78', '79'])).
% 2.73/2.98  thf('81', plain,
% 2.73/2.98      (((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))),
% 2.73/2.98      inference('sup-', [status(thm)], ['62', '80'])).
% 2.73/2.98  thf('82', plain,
% 2.73/2.98      (((v5_pre_topc @ sk_D @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('83', plain, (((sk_C_1) = (sk_D))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('84', plain,
% 2.73/2.98      (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.98      inference('demod', [status(thm)], ['82', '83'])).
% 2.73/2.98  thf('85', plain,
% 2.73/2.98      (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98         <= (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.98      inference('split', [status(esa)], ['84'])).
% 2.73/2.98  thf('86', plain,
% 2.73/2.98      ((~ (v5_pre_topc @ sk_D @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.98        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('87', plain,
% 2.73/2.98      ((~ (v5_pre_topc @ sk_D @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98         <= (~
% 2.73/2.98             ((v5_pre_topc @ sk_D @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.98      inference('split', [status(esa)], ['86'])).
% 2.73/2.98  thf('88', plain, (((sk_C_1) = (sk_D))),
% 2.73/2.98      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.98  thf('89', plain,
% 2.73/2.98      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.98         <= (~
% 2.73/2.98             ((v5_pre_topc @ sk_D @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.98      inference('demod', [status(thm)], ['87', '88'])).
% 2.73/2.98  thf('90', plain,
% 2.73/2.98      (~
% 2.73/2.98       ((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))) | 
% 2.73/2.98       ((v5_pre_topc @ sk_D @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.98         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.98      inference('sup-', [status(thm)], ['85', '89'])).
% 2.73/2.98  thf('91', plain,
% 2.73/2.98      ((~ (v5_pre_topc @ sk_D @ 
% 2.73/2.98           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('92', plain, (((sk_C_1) = (sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('93', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('demod', [status(thm)], ['91', '92'])).
% 2.73/2.99  thf('94', plain,
% 2.73/2.99      (~
% 2.73/2.99       ((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))) | 
% 2.73/2.99       ~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('split', [status(esa)], ['93'])).
% 2.73/2.99  thf('95', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (~ (l1_pre_topc @ X0)
% 2.73/2.99          | (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['0', '1'])).
% 2.73/2.99  thf('96', plain,
% 2.73/2.99      (![X36 : $i]:
% 2.73/2.99         ((v2_pre_topc @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 2.73/2.99          | ~ (l1_pre_topc @ X36)
% 2.73/2.99          | ~ (v2_pre_topc @ X36))),
% 2.73/2.99      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 2.73/2.99  thf('97', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_D @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('split', [status(esa)], ['61'])).
% 2.73/2.99  thf('98', plain, (((sk_C_1) = (sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('99', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('demod', [status(thm)], ['97', '98'])).
% 2.73/2.99  thf('100', plain,
% 2.73/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.99        (k1_zfmisc_1 @ 
% 2.73/2.99         (k2_zfmisc_1 @ 
% 2.73/2.99          (u1_struct_0 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99          (u1_struct_0 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))))),
% 2.73/2.99      inference('demod', [status(thm)], ['37', '38'])).
% 2.73/2.99  thf('101', plain,
% 2.73/2.99      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X44)
% 2.73/2.99          | ~ (l1_pre_topc @ X44)
% 2.73/2.99          | ~ (v1_funct_1 @ X45)
% 2.73/2.99          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X46) @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))
% 2.73/2.99          | ~ (m1_subset_1 @ X45 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ 
% 2.73/2.99                 (u1_struct_0 @ 
% 2.73/2.99                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))))
% 2.73/2.99          | ~ (v5_pre_topc @ X45 @ X46 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)))
% 2.73/2.99          | (v5_pre_topc @ X47 @ X46 @ X44)
% 2.73/2.99          | ((X47) != (X45))
% 2.73/2.99          | ~ (m1_subset_1 @ X47 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))))
% 2.73/2.99          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))
% 2.73/2.99          | ~ (v1_funct_1 @ X47)
% 2.73/2.99          | ~ (l1_pre_topc @ X46)
% 2.73/2.99          | ~ (v2_pre_topc @ X46))),
% 2.73/2.99      inference('cnf', [status(esa)], [t63_pre_topc])).
% 2.73/2.99  thf('102', plain,
% 2.73/2.99      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X46)
% 2.73/2.99          | ~ (l1_pre_topc @ X46)
% 2.73/2.99          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))
% 2.73/2.99          | ~ (m1_subset_1 @ X45 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))))
% 2.73/2.99          | (v5_pre_topc @ X45 @ X46 @ X44)
% 2.73/2.99          | ~ (v5_pre_topc @ X45 @ X46 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)))
% 2.73/2.99          | ~ (m1_subset_1 @ X45 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ 
% 2.73/2.99                 (u1_struct_0 @ 
% 2.73/2.99                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))))
% 2.73/2.99          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X46) @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))))
% 2.73/2.99          | ~ (v1_funct_1 @ X45)
% 2.73/2.99          | ~ (l1_pre_topc @ X44)
% 2.73/2.99          | ~ (v2_pre_topc @ X44))),
% 2.73/2.99      inference('simplify', [status(thm)], ['101'])).
% 2.73/2.99  thf('103', plain,
% 2.73/2.99      ((~ (v2_pre_topc @ sk_B_2)
% 2.73/2.99        | ~ (l1_pre_topc @ sk_B_2)
% 2.73/2.99        | ~ (v1_funct_1 @ sk_C_1)
% 2.73/2.99        | ~ (v1_funct_2 @ sk_C_1 @ 
% 2.73/2.99             (u1_struct_0 @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99             (u1_struct_0 @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.99        | ~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 2.73/2.99        | ~ (m1_subset_1 @ sk_C_1 @ 
% 2.73/2.99             (k1_zfmisc_1 @ 
% 2.73/2.99              (k2_zfmisc_1 @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99               (u1_struct_0 @ sk_B_2))))
% 2.73/2.99        | ~ (v1_funct_2 @ sk_C_1 @ 
% 2.73/2.99             (u1_struct_0 @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99             (u1_struct_0 @ sk_B_2))
% 2.73/2.99        | ~ (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99        | ~ (v2_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['100', '102'])).
% 2.73/2.99  thf('104', plain, ((v2_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('105', plain, ((l1_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('106', plain, ((v1_funct_1 @ sk_C_1)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('107', plain,
% 2.73/2.99      ((v1_funct_2 @ sk_C_1 @ 
% 2.73/2.99        (u1_struct_0 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99        (u1_struct_0 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('demod', [status(thm)], ['44', '45'])).
% 2.73/2.99  thf('108', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 2.73/2.99        | ~ (m1_subset_1 @ sk_C_1 @ 
% 2.73/2.99             (k1_zfmisc_1 @ 
% 2.73/2.99              (k2_zfmisc_1 @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99               (u1_struct_0 @ sk_B_2))))
% 2.73/2.99        | ~ (v1_funct_2 @ sk_C_1 @ 
% 2.73/2.99             (u1_struct_0 @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99             (u1_struct_0 @ sk_B_2))
% 2.73/2.99        | ~ (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99        | ~ (v2_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 2.73/2.99      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 2.73/2.99  thf('109', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | (r1_tarski @ 
% 2.73/2.99             (u1_struct_0 @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.99             (u1_struct_0 @ X0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['22', '23'])).
% 2.73/2.99  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('111', plain,
% 2.73/2.99      (![X28 : $i, X30 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X28)
% 2.73/2.99          | (zip_tseitin_5 @ X30 @ X28)
% 2.73/2.99          | ~ (l1_pre_topc @ X28))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.73/2.99  thf('112', plain,
% 2.73/2.99      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['110', '111'])).
% 2.73/2.99  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('114', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 2.73/2.99      inference('demod', [status(thm)], ['112', '113'])).
% 2.73/2.99  thf('115', plain,
% 2.73/2.99      (![X35 : $i]:
% 2.73/2.99         ((m1_subset_1 @ (u1_pre_topc @ X35) @ 
% 2.73/2.99           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))
% 2.73/2.99          | ~ (l1_pre_topc @ X35))),
% 2.73/2.99      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 2.73/2.99  thf('116', plain,
% 2.73/2.99      (![X25 : $i, X26 : $i]:
% 2.73/2.99         (~ (m1_subset_1 @ X25 @ 
% 2.73/2.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26))))
% 2.73/2.99          | (zip_tseitin_4 @ X25 @ X26)
% 2.73/2.99          | ~ (zip_tseitin_5 @ X25 @ X26))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.73/2.99  thf('117', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 2.73/2.99          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 2.73/2.99      inference('sup-', [status(thm)], ['115', '116'])).
% 2.73/2.99  thf('118', plain,
% 2.73/2.99      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['114', '117'])).
% 2.73/2.99  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('120', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 2.73/2.99      inference('demod', [status(thm)], ['118', '119'])).
% 2.73/2.99  thf('121', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.73/2.99      inference('simplify', [status(thm)], ['7'])).
% 2.73/2.99  thf('122', plain,
% 2.73/2.99      (![X22 : $i, X23 : $i]:
% 2.73/2.99         (~ (r1_tarski @ X22 @ (u1_pre_topc @ X23))
% 2.73/2.99          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X23) @ X22) @ 
% 2.73/2.99             (u1_pre_topc @ X23))
% 2.73/2.99          | ~ (zip_tseitin_4 @ X22 @ X23))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.73/2.99  thf('123', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 2.73/2.99          | (r2_hidden @ 
% 2.73/2.99             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 2.73/2.99             (u1_pre_topc @ X0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['121', '122'])).
% 2.73/2.99  thf('124', plain,
% 2.73/2.99      ((r2_hidden @ 
% 2.73/2.99        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99        (u1_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['120', '123'])).
% 2.73/2.99  thf('125', plain,
% 2.73/2.99      (![X28 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X28)
% 2.73/2.99          | (r2_hidden @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28))
% 2.73/2.99          | ~ (l1_pre_topc @ X28))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.73/2.99  thf('126', plain,
% 2.73/2.99      (![X6 : $i, X8 : $i, X9 : $i]:
% 2.73/2.99         ((zip_tseitin_0 @ X8 @ X6 @ X9)
% 2.73/2.99          | ~ (r2_hidden @ X8 @ (u1_pre_topc @ X9))
% 2.73/2.99          | ~ (r2_hidden @ X6 @ (u1_pre_topc @ X9)))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.73/2.99  thf('127', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 2.73/2.99          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 2.73/2.99      inference('sup-', [status(thm)], ['125', '126'])).
% 2.73/2.99  thf('128', plain,
% 2.73/2.99      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.99         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 2.73/2.99        | ~ (v2_pre_topc @ sk_A)
% 2.73/2.99        | ~ (l1_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['124', '127'])).
% 2.73/2.99  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('131', plain,
% 2.73/2.99      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.99        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 2.73/2.99      inference('demod', [status(thm)], ['128', '129', '130'])).
% 2.73/2.99  thf('132', plain,
% 2.73/2.99      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.73/2.99         ((r2_hidden @ X8 @ (u1_pre_topc @ X7))
% 2.73/2.99          | ~ (zip_tseitin_0 @ X8 @ X6 @ X7))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_11])).
% 2.73/2.99  thf('133', plain,
% 2.73/2.99      ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['131', '132'])).
% 2.73/2.99  thf('134', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (~ (l1_pre_topc @ X0)
% 2.73/2.99          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.73/2.99          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['10', '11'])).
% 2.73/2.99  thf('135', plain,
% 2.73/2.99      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['133', '134'])).
% 2.73/2.99  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('137', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 2.73/2.99      inference('demod', [status(thm)], ['135', '136'])).
% 2.73/2.99  thf('138', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.73/2.99             (k1_zfmisc_1 @ 
% 2.73/2.99              (u1_struct_0 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 2.73/2.99          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 2.73/2.99      inference('sup-', [status(thm)], ['26', '27'])).
% 2.73/2.99  thf('139', plain,
% 2.73/2.99      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.99         (k1_zfmisc_1 @ 
% 2.73/2.99          (u1_struct_0 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 2.73/2.99        | ~ (l1_pre_topc @ sk_A)
% 2.73/2.99        | ~ (v2_pre_topc @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['137', '138'])).
% 2.73/2.99  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('142', plain,
% 2.73/2.99      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.99        (k1_zfmisc_1 @ 
% 2.73/2.99         (u1_struct_0 @ 
% 2.73/2.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 2.73/2.99      inference('demod', [status(thm)], ['139', '140', '141'])).
% 2.73/2.99  thf('143', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i]:
% 2.73/2.99         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.73/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.73/2.99  thf('144', plain,
% 2.73/2.99      ((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 2.73/2.99        (u1_struct_0 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['142', '143'])).
% 2.73/2.99  thf('145', plain,
% 2.73/2.99      (![X0 : $i, X2 : $i]:
% 2.73/2.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.73/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.73/2.99  thf('146', plain,
% 2.73/2.99      ((~ (r1_tarski @ 
% 2.73/2.99           (u1_struct_0 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 2.73/2.99           (u1_struct_0 @ sk_A))
% 2.73/2.99        | ((u1_struct_0 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99            = (u1_struct_0 @ sk_A)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['144', '145'])).
% 2.73/2.99  thf('147', plain,
% 2.73/2.99      ((~ (l1_pre_topc @ sk_A)
% 2.73/2.99        | ~ (v2_pre_topc @ sk_A)
% 2.73/2.99        | ((u1_struct_0 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99            = (u1_struct_0 @ sk_A)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['109', '146'])).
% 2.73/2.99  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('150', plain,
% 2.73/2.99      (((u1_struct_0 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99         = (u1_struct_0 @ sk_A))),
% 2.73/2.99      inference('demod', [status(thm)], ['147', '148', '149'])).
% 2.73/2.99  thf('151', plain,
% 2.73/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.99        (k1_zfmisc_1 @ 
% 2.73/2.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('152', plain,
% 2.73/2.99      (((u1_struct_0 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99         = (u1_struct_0 @ sk_A))),
% 2.73/2.99      inference('demod', [status(thm)], ['147', '148', '149'])).
% 2.73/2.99  thf('153', plain,
% 2.73/2.99      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('154', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 2.73/2.99        | ~ (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99        | ~ (v2_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 2.73/2.99      inference('demod', [status(thm)], ['108', '150', '151', '152', '153'])).
% 2.73/2.99  thf('155', plain,
% 2.73/2.99      (((~ (v2_pre_topc @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99         | ~ (l1_pre_topc @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 2.73/2.99         | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99            sk_B_2)))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['99', '154'])).
% 2.73/2.99  thf('156', plain,
% 2.73/2.99      (((~ (v2_pre_topc @ sk_A)
% 2.73/2.99         | ~ (l1_pre_topc @ sk_A)
% 2.73/2.99         | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99            sk_B_2)
% 2.73/2.99         | ~ (l1_pre_topc @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['96', '155'])).
% 2.73/2.99  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('159', plain,
% 2.73/2.99      ((((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 2.73/2.99         | ~ (l1_pre_topc @ 
% 2.73/2.99              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('demod', [status(thm)], ['156', '157', '158'])).
% 2.73/2.99  thf('160', plain,
% 2.73/2.99      (((~ (l1_pre_topc @ sk_A)
% 2.73/2.99         | (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99            sk_B_2)))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['95', '159'])).
% 2.73/2.99  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('162', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('demod', [status(thm)], ['160', '161'])).
% 2.73/2.99  thf('163', plain,
% 2.73/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.73/2.99        (k1_zfmisc_1 @ 
% 2.73/2.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('164', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (((u1_struct_0 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.99            = (u1_struct_0 @ X0))
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (l1_pre_topc @ X0))),
% 2.73/2.99      inference('simplify', [status(thm)], ['35'])).
% 2.73/2.99  thf('165', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (((u1_struct_0 @ 
% 2.73/2.99            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.73/2.99            = (u1_struct_0 @ X0))
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (l1_pre_topc @ X0))),
% 2.73/2.99      inference('simplify', [status(thm)], ['35'])).
% 2.73/2.99  thf('166', plain,
% 2.73/2.99      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X40)
% 2.73/2.99          | ~ (l1_pre_topc @ X40)
% 2.73/2.99          | ~ (v1_funct_1 @ X41)
% 2.73/2.99          | ~ (v1_funct_2 @ X41 @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.99               (u1_struct_0 @ X40))
% 2.73/2.99          | ~ (m1_subset_1 @ X41 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ 
% 2.73/2.99                 (u1_struct_0 @ 
% 2.73/2.99                  (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.99                 (u1_struct_0 @ X40))))
% 2.73/2.99          | ~ (v5_pre_topc @ X41 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)) @ X40)
% 2.73/2.99          | (v5_pre_topc @ X43 @ X42 @ X40)
% 2.73/2.99          | ((X43) != (X41))
% 2.73/2.99          | ~ (m1_subset_1 @ X43 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 2.73/2.99          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 2.73/2.99          | ~ (v1_funct_1 @ X43)
% 2.73/2.99          | ~ (l1_pre_topc @ X42)
% 2.73/2.99          | ~ (v2_pre_topc @ X42))),
% 2.73/2.99      inference('cnf', [status(esa)], [t62_pre_topc])).
% 2.73/2.99  thf('167', plain,
% 2.73/2.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.73/2.99         (~ (v2_pre_topc @ X42)
% 2.73/2.99          | ~ (l1_pre_topc @ X42)
% 2.73/2.99          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 2.73/2.99          | ~ (m1_subset_1 @ X41 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 2.73/2.99          | (v5_pre_topc @ X41 @ X42 @ X40)
% 2.73/2.99          | ~ (v5_pre_topc @ X41 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)) @ X40)
% 2.73/2.99          | ~ (m1_subset_1 @ X41 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ 
% 2.73/2.99                 (u1_struct_0 @ 
% 2.73/2.99                  (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.99                 (u1_struct_0 @ X40))))
% 2.73/2.99          | ~ (v1_funct_2 @ X41 @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))) @ 
% 2.73/2.99               (u1_struct_0 @ X40))
% 2.73/2.99          | ~ (v1_funct_1 @ X41)
% 2.73/2.99          | ~ (l1_pre_topc @ X40)
% 2.73/2.99          | ~ (v2_pre_topc @ X40))),
% 2.73/2.99      inference('simplify', [status(thm)], ['166'])).
% 2.73/2.99  thf('168', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         (~ (m1_subset_1 @ X2 @ 
% 2.73/2.99             (k1_zfmisc_1 @ 
% 2.73/2.99              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X1)
% 2.73/2.99          | ~ (l1_pre_topc @ X1)
% 2.73/2.99          | ~ (v1_funct_1 @ X2)
% 2.73/2.99          | ~ (v1_funct_2 @ X2 @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.99               (u1_struct_0 @ X1))
% 2.73/2.99          | ~ (v5_pre_topc @ X2 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 2.73/2.99          | (v5_pre_topc @ X2 @ X0 @ X1)
% 2.73/2.99          | ~ (m1_subset_1 @ X2 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 2.73/2.99          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X0))),
% 2.73/2.99      inference('sup-', [status(thm)], ['165', '167'])).
% 2.73/2.99  thf('169', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         (~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 2.73/2.99          | (v5_pre_topc @ X2 @ X0 @ X1)
% 2.73/2.99          | ~ (v5_pre_topc @ X2 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 2.73/2.99          | ~ (v1_funct_2 @ X2 @ 
% 2.73/2.99               (u1_struct_0 @ 
% 2.73/2.99                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 2.73/2.99               (u1_struct_0 @ X1))
% 2.73/2.99          | ~ (v1_funct_1 @ X2)
% 2.73/2.99          | ~ (l1_pre_topc @ X1)
% 2.73/2.99          | ~ (v2_pre_topc @ X1)
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (m1_subset_1 @ X2 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1)))))),
% 2.73/2.99      inference('simplify', [status(thm)], ['168'])).
% 2.73/2.99  thf('170', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         (~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (m1_subset_1 @ X2 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (v2_pre_topc @ X1)
% 2.73/2.99          | ~ (l1_pre_topc @ X1)
% 2.73/2.99          | ~ (v1_funct_1 @ X2)
% 2.73/2.99          | ~ (v5_pre_topc @ X2 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 2.73/2.99          | (v5_pre_topc @ X2 @ X0 @ X1)
% 2.73/2.99          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['164', '169'])).
% 2.73/2.99  thf('171', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         ((v5_pre_topc @ X2 @ X0 @ X1)
% 2.73/2.99          | ~ (v5_pre_topc @ X2 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 2.73/2.99          | ~ (v1_funct_1 @ X2)
% 2.73/2.99          | ~ (l1_pre_topc @ X1)
% 2.73/2.99          | ~ (v2_pre_topc @ X1)
% 2.73/2.99          | ~ (m1_subset_1 @ X2 @ 
% 2.73/2.99               (k1_zfmisc_1 @ 
% 2.73/2.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 2.73/2.99          | ~ (v2_pre_topc @ X0)
% 2.73/2.99          | ~ (l1_pre_topc @ X0)
% 2.73/2.99          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 2.73/2.99      inference('simplify', [status(thm)], ['170'])).
% 2.73/2.99  thf('172', plain,
% 2.73/2.99      ((~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 2.73/2.99        | ~ (l1_pre_topc @ sk_A)
% 2.73/2.99        | ~ (v2_pre_topc @ sk_A)
% 2.73/2.99        | ~ (v2_pre_topc @ sk_B_2)
% 2.73/2.99        | ~ (l1_pre_topc @ sk_B_2)
% 2.73/2.99        | ~ (v1_funct_1 @ sk_C_1)
% 2.73/2.99        | ~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99             sk_B_2)
% 2.73/2.99        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('sup-', [status(thm)], ['163', '171'])).
% 2.73/2.99  thf('173', plain,
% 2.73/2.99      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('175', plain, ((v2_pre_topc @ sk_A)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('176', plain, ((v2_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('177', plain, ((l1_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('178', plain, ((v1_funct_1 @ sk_C_1)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('179', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 2.73/2.99        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('demod', [status(thm)],
% 2.73/2.99                ['172', '173', '174', '175', '176', '177', '178'])).
% 2.73/2.99  thf('180', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['162', '179'])).
% 2.73/2.99  thf('181', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))
% 2.73/2.99         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))),
% 2.73/2.99      inference('split', [status(esa)], ['86'])).
% 2.73/2.99  thf('182', plain,
% 2.73/2.99      (~
% 2.73/2.99       ((v5_pre_topc @ sk_D @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))) | 
% 2.73/2.99       ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('sup-', [status(thm)], ['180', '181'])).
% 2.73/2.99  thf('183', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)) | 
% 2.73/2.99       ((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('split', [status(esa)], ['84'])).
% 2.73/2.99  thf('184', plain, (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 2.73/2.99      inference('sat_resolution*', [status(thm)], ['90', '94', '182', '183'])).
% 2.73/2.99  thf('185', plain,
% 2.73/2.99      ((v5_pre_topc @ sk_C_1 @ sk_A @ 
% 2.73/2.99        (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 2.73/2.99      inference('simpl_trail', [status(thm)], ['81', '184'])).
% 2.73/2.99  thf('186', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | ~ (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | ~ (v2_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('demod', [status(thm)], ['54', '60', '185'])).
% 2.73/2.99  thf('187', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.99         <= (~
% 2.73/2.99             ((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('demod', [status(thm)], ['87', '88'])).
% 2.73/2.99  thf('188', plain,
% 2.73/2.99      (((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.99         <= (((v5_pre_topc @ sk_D @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('demod', [status(thm)], ['97', '98'])).
% 2.73/2.99  thf('189', plain,
% 2.73/2.99      ((~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))
% 2.73/2.99         <= (~
% 2.73/2.99             ((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))))),
% 2.73/2.99      inference('split', [status(esa)], ['93'])).
% 2.73/2.99  thf('190', plain,
% 2.73/2.99      (~
% 2.73/2.99       ((v5_pre_topc @ sk_D @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))) | 
% 2.73/2.99       ((v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['188', '189'])).
% 2.73/2.99  thf('191', plain,
% 2.73/2.99      (~
% 2.73/2.99       ((v5_pre_topc @ sk_D @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99         (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('sat_resolution*', [status(thm)], ['90', '94', '182', '190'])).
% 2.73/2.99  thf('192', plain,
% 2.73/2.99      (~ (v5_pre_topc @ sk_C_1 @ 
% 2.73/2.99          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 2.73/2.99          (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 2.73/2.99      inference('simpl_trail', [status(thm)], ['187', '191'])).
% 2.73/2.99  thf('193', plain,
% 2.73/2.99      ((~ (v2_pre_topc @ 
% 2.73/2.99           (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 2.73/2.99        | ~ (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('clc', [status(thm)], ['186', '192'])).
% 2.73/2.99  thf('194', plain,
% 2.73/2.99      ((~ (v2_pre_topc @ sk_B_2)
% 2.73/2.99        | ~ (l1_pre_topc @ sk_B_2)
% 2.73/2.99        | ~ (l1_pre_topc @ 
% 2.73/2.99             (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['3', '193'])).
% 2.73/2.99  thf('195', plain, ((v2_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('196', plain, ((l1_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('197', plain,
% 2.73/2.99      (~ (l1_pre_topc @ 
% 2.73/2.99          (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 2.73/2.99      inference('demod', [status(thm)], ['194', '195', '196'])).
% 2.73/2.99  thf('198', plain, (~ (l1_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('sup-', [status(thm)], ['2', '197'])).
% 2.73/2.99  thf('199', plain, ((l1_pre_topc @ sk_B_2)),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.73/2.99  thf('200', plain, ($false), inference('demod', [status(thm)], ['198', '199'])).
% 2.73/2.99  
% 2.73/2.99  % SZS output end Refutation
% 2.73/2.99  
% 2.73/2.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
