%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4PPZfYmEL4

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:08 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  185 (2841 expanded)
%              Number of leaves         :   50 ( 881 expanded)
%              Depth                    :   21
%              Number of atoms          : 1483 (41696 expanded)
%              Number of equality atoms :   28 (1236 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t14_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_tsep_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( C
                    = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                 => ( ( ( v1_tsep_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_tsep_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tmap_1])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
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

thf('8',plain,(
    ! [X30: $i] :
      ( ~ ( v2_pre_topc @ X30 )
      | ( r2_hidden @ ( u1_struct_0 @ X30 ) @ ( u1_pre_topc @ X30 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( r2_hidden @ X33 @ ( u1_pre_topc @ X34 ) )
      | ( v3_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      = ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('27',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_pre_topc @ X37 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) ) ) )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','41','42','43','44'])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ( X42
       != ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( m1_pre_topc @ X42 @ X44 )
      | ( m1_pre_topc @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('47',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( m1_pre_topc @ X43 @ X44 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) @ X44 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) @ X0 )
      | ( m1_pre_topc @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','41','42','43','44'])).

thf('51',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','41','42','43','44'])).

thf('54',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('55',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','41','42','43','44'])).

thf('57',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('58',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_pre_topc @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['48','51','52','53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B_2 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('68',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('69',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_C_1
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_tsep_1 @ sk_B_2 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('78',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X48 @ X49 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('79',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ( X47
       != ( u1_struct_0 @ X45 ) )
      | ~ ( v1_tsep_1 @ X45 @ X46 )
      | ~ ( m1_pre_topc @ X45 @ X46 )
      | ( v3_pre_topc @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('83',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X45 ) @ X46 )
      | ~ ( v1_tsep_1 @ X45 @ X46 )
      | ~ ( m1_pre_topc @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
      | ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','41','42','43','44'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','89'])).

thf('91',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('92',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X48 @ X49 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('93',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ( X47
       != ( u1_struct_0 @ X45 ) )
      | ~ ( v3_pre_topc @ X47 @ X46 )
      | ( v1_tsep_1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('97',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v1_tsep_1 @ X45 @ X46 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X45 ) @ X46 )
      | ~ ( m1_pre_topc @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_C_1 @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_B_2 @ sk_A )
      & ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','102'])).

thf('104',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','65','74','105'])).

thf('107',plain,(
    ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('109',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v1_tsep_1 @ X45 @ X46 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X45 ) @ X46 )
      | ~ ( m1_pre_topc @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('110',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_2 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','41','42','43','44'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_2 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','65'])).

thf('117',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('119',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X45 ) @ X46 )
      | ~ ( v1_tsep_1 @ X45 @ X46 )
      | ~ ( m1_pre_topc @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('120',plain,
    ( ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','65','74'])).

thf('126',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_A )
   <= ( v1_tsep_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('128',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_A )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('129',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','4','65','74','105','128'])).

thf('130',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['127','129'])).

thf('131',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['126','130'])).

thf('132',plain,(
    v1_tsep_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['117','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['107','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4PPZfYmEL4
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 478 iterations in 0.208s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.66  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.66  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.46/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.46/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.46/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.46/0.66  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.46/0.66  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(t14_tmap_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.66               ( ( ( C ) =
% 0.46/0.66                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.66                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.66                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.66                  ( ( ( C ) =
% 0.46/0.66                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.66                    ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.66                      ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t14_tmap_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_C_1 @ sk_A)
% 0.46/0.66        | ~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      ((~ (v1_tsep_1 @ sk_B_2 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)) | ~ ((v1_tsep_1 @ sk_C_1 @ sk_A)) | 
% 0.46/0.66       ~ ((m1_pre_topc @ sk_B_2 @ sk_A)) | ~ ((m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A) | (m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) | ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A) | (v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['5'])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.66         ( ( ![B:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ![C:$i]:
% 0.46/0.66                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.66                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.66                     ( r2_hidden @
% 0.46/0.66                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.46/0.66                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.46/0.66           ( ![B:$i]:
% 0.46/0.66             ( ( m1_subset_1 @
% 0.46/0.66                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.66                 ( r2_hidden @
% 0.46/0.66                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.46/0.66                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.46/0.66           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_2, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.46/0.66       ( ( m1_subset_1 @
% 0.46/0.66           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.46/0.66  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_4, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.46/0.66       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.66         ( r2_hidden @
% 0.46/0.66           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_6, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.46/0.66       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_8, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.46/0.66       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.46/0.66  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_10, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.46/0.66       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.46/0.66         ( r2_hidden @
% 0.46/0.66           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_12, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.46/0.66       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.66         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_13, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.66         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.66           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.46/0.66           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X30 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X30)
% 0.46/0.66          | (r2_hidden @ (u1_struct_0 @ X30) @ (u1_pre_topc @ X30))
% 0.46/0.66          | ~ (l1_pre_topc @ X30))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.66  thf(dt_k2_subset_1, axiom,
% 0.46/0.66    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.66  thf('10', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.66  thf('11', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.46/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf(d5_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.66             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.46/0.66          | ~ (r2_hidden @ X33 @ (u1_pre_topc @ X34))
% 0.46/0.66          | (v3_pre_topc @ X33 @ X34)
% 0.46/0.66          | ~ (l1_pre_topc @ X34))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.66  thf('16', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.46/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf(t60_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.46/0.66             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.46/0.66           ( ( v3_pre_topc @
% 0.46/0.66               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.46/0.66             ( m1_subset_1 @
% 0.46/0.66               B @ 
% 0.46/0.66               ( k1_zfmisc_1 @
% 0.46/0.66                 ( u1_struct_0 @
% 0.46/0.66                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         (~ (v3_pre_topc @ X39 @ X38)
% 0.46/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.46/0.66          | (m1_subset_1 @ X39 @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (u1_struct_0 @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))))
% 0.46/0.66          | ~ (l1_pre_topc @ X38)
% 0.46/0.66          | ~ (v2_pre_topc @ X38))),
% 0.46/0.66      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (u1_struct_0 @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.46/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (u1_struct_0 @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (u1_struct_0 @ 
% 0.46/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.66  thf(t3_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.46/0.66             (u1_struct_0 @ 
% 0.46/0.66              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i]:
% 0.46/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (r1_tarski @ 
% 0.46/0.66               (u1_struct_0 @ 
% 0.46/0.66                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.46/0.66               (u1_struct_0 @ X0))
% 0.46/0.66          | ((u1_struct_0 @ 
% 0.46/0.66              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.66              = (u1_struct_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))
% 0.46/0.66        | ((u1_struct_0 @ 
% 0.46/0.66            (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 0.46/0.66            = (u1_struct_0 @ sk_B_2))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_B_2)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_B_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '24'])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.66  thf('27', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.46/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X37 : $i, X38 : $i]:
% 0.46/0.66         (~ (v3_pre_topc @ X37 @ 
% 0.46/0.66             (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 0.46/0.66          | ~ (m1_subset_1 @ X37 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (u1_struct_0 @ 
% 0.46/0.66                 (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))))
% 0.46/0.66          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.46/0.66          | ~ (l1_pre_topc @ X38)
% 0.46/0.66          | ~ (v2_pre_topc @ X38))),
% 0.46/0.66      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.66          | ~ (v2_pre_topc @ sk_B_2)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_B_2)
% 0.46/0.66          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.46/0.66          | ~ (v3_pre_topc @ X0 @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain, ((v2_pre_topc @ sk_B_2)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('32', plain, ((l1_pre_topc @ sk_B_2)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.66          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.46/0.66          | ~ (v3_pre_topc @ X0 @ sk_C_1))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_C_1)
% 0.46/0.66        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['27', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_C_1)
% 0.46/0.66        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['26', '35'])).
% 0.46/0.66  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('38', plain, ((v2_pre_topc @ sk_C_1)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))),
% 0.46/0.66      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('43', plain, ((l1_pre_topc @ sk_B_2)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('44', plain, ((v2_pre_topc @ sk_B_2)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('45', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '41', '42', '43', '44'])).
% 0.46/0.66  thf(t12_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.66               ( ( ( B ) =
% 0.46/0.66                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.46/0.66                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X42)
% 0.46/0.66          | ~ (l1_pre_topc @ X42)
% 0.46/0.66          | ((X42) != (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 0.46/0.66          | ~ (m1_pre_topc @ X42 @ X44)
% 0.46/0.66          | (m1_pre_topc @ X43 @ X44)
% 0.46/0.66          | ~ (l1_pre_topc @ X43)
% 0.46/0.66          | ~ (v2_pre_topc @ X43)
% 0.46/0.66          | ~ (l1_pre_topc @ X44))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X43 : $i, X44 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X44)
% 0.46/0.66          | ~ (v2_pre_topc @ X43)
% 0.46/0.66          | ~ (l1_pre_topc @ X43)
% 0.46/0.66          | (m1_pre_topc @ X43 @ X44)
% 0.46/0.66          | ~ (m1_pre_topc @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)) @ X44)
% 0.46/0.66          | ~ (l1_pre_topc @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 0.46/0.66          | ~ (v2_pre_topc @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ 
% 0.46/0.66             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))
% 0.46/0.66          | ~ (v2_pre_topc @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))
% 0.46/0.66          | ~ (m1_pre_topc @ 
% 0.46/0.66               (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)) @ 
% 0.46/0.66               X0)
% 0.46/0.66          | (m1_pre_topc @ sk_B_2 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_B_2)
% 0.46/0.66          | ~ (v2_pre_topc @ sk_B_2)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '41', '42', '43', '44'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('53', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '41', '42', '43', '44'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('55', plain, ((v2_pre_topc @ sk_C_1)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('56', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '41', '42', '43', '44'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('58', plain, ((l1_pre_topc @ sk_B_2)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('59', plain, ((v2_pre_topc @ sk_B_2)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.46/0.66          | (m1_pre_topc @ sk_B_2 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['48', '51', '52', '53', '54', '55', '56', '57', '58', '59'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_2 @ sk_A)))
% 0.46/0.66         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '60'])).
% 0.46/0.66  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      ((~ (m1_pre_topc @ sk_B_2 @ sk_A)) <= (~ ((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_B_2 @ sk_A)) | ~ ((m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_C_1 @ sk_A) | (m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['66'])).
% 0.46/0.66  thf(t11_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ( v1_pre_topc @
% 0.46/0.66               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.46/0.66             ( m1_pre_topc @
% 0.46/0.66               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X40 : $i, X41 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X40 @ X41)
% 0.46/0.66          | (m1_pre_topc @ 
% 0.46/0.66             (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)) @ X41)
% 0.46/0.66          | ~ (l1_pre_topc @ X41))),
% 0.46/0.66      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | (m1_pre_topc @ 
% 0.46/0.66            (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)) @ 
% 0.46/0.66            sk_A)))
% 0.46/0.66         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.66  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (((sk_C_1)
% 0.46/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_B_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)) <= (~ ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_C_1 @ sk_A) | (v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_B_2 @ sk_A)) <= (((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['75'])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['66'])).
% 0.46/0.66  thf(t1_tsep_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( m1_subset_1 @
% 0.46/0.66             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (![X48 : $i, X49 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X48 @ X49)
% 0.46/0.66          | (m1_subset_1 @ (u1_struct_0 @ X48) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.46/0.66          | ~ (l1_pre_topc @ X49))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | (m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.46/0.66            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.66  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['79', '80'])).
% 0.46/0.66  thf(t16_tsep_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.46/0.66                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.66                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X45 @ X46)
% 0.46/0.66          | ((X47) != (u1_struct_0 @ X45))
% 0.46/0.66          | ~ (v1_tsep_1 @ X45 @ X46)
% 0.46/0.66          | ~ (m1_pre_topc @ X45 @ X46)
% 0.46/0.66          | (v3_pre_topc @ X47 @ X46)
% 0.46/0.66          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.46/0.66          | ~ (l1_pre_topc @ X46)
% 0.46/0.66          | ~ (v2_pre_topc @ X46))),
% 0.46/0.66      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      (![X45 : $i, X46 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X46)
% 0.46/0.66          | ~ (l1_pre_topc @ X46)
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X45) @ X46)
% 0.46/0.66          | ~ (v1_tsep_1 @ X45 @ X46)
% 0.46/0.66          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.46/0.66      inference('simplify', [status(thm)], ['82'])).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      (((~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.46/0.66         | ~ (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.46/0.66         | (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.46/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['81', '83'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['66'])).
% 0.46/0.66  thf('86', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '41', '42', '43', '44'])).
% 0.46/0.66  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (((~ (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.46/0.66         | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)))
% 0.46/0.66         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A))
% 0.46/0.66         <= (((v1_tsep_1 @ sk_B_2 @ sk_A)) & ((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['76', '89'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['5'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (![X48 : $i, X49 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X48 @ X49)
% 0.46/0.66          | (m1_subset_1 @ (u1_struct_0 @ X48) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.46/0.66          | ~ (l1_pre_topc @ X49))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.66            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.66  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['93', '94'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X45 @ X46)
% 0.46/0.66          | ((X47) != (u1_struct_0 @ X45))
% 0.46/0.66          | ~ (v3_pre_topc @ X47 @ X46)
% 0.46/0.66          | (v1_tsep_1 @ X45 @ X46)
% 0.46/0.66          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.46/0.66          | ~ (l1_pre_topc @ X46)
% 0.46/0.66          | ~ (v2_pre_topc @ X46))),
% 0.46/0.66      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      (![X45 : $i, X46 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X46)
% 0.46/0.66          | ~ (l1_pre_topc @ X46)
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.46/0.66          | (v1_tsep_1 @ X45 @ X46)
% 0.46/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X45) @ X46)
% 0.46/0.66          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.46/0.66      inference('simplify', [status(thm)], ['96'])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      (((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.46/0.66         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.66         | (v1_tsep_1 @ sk_C_1 @ sk_A)
% 0.46/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['95', '97'])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['5'])).
% 0.46/0.66  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.66         | (v1_tsep_1 @ sk_C_1 @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_C_1 @ sk_A))
% 0.46/0.66         <= (((v1_tsep_1 @ sk_B_2 @ sk_A)) & 
% 0.46/0.66             ((m1_pre_topc @ sk_B_2 @ sk_A)) & 
% 0.46/0.66             ((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['90', '102'])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      ((~ (v1_tsep_1 @ sk_C_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_C_1 @ sk_A)) | ~ ((v1_tsep_1 @ sk_B_2 @ sk_A)) | 
% 0.46/0.66       ~ ((m1_pre_topc @ sk_C_1 @ sk_A)) | ~ ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['103', '104'])).
% 0.46/0.66  thf('106', plain, (~ ((v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['2', '4', '65', '74', '105'])).
% 0.46/0.66  thf('107', plain, (~ (v1_tsep_1 @ sk_B_2 @ sk_A)),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['1', '106'])).
% 0.46/0.66  thf('108', plain,
% 0.46/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['79', '80'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (![X45 : $i, X46 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X46)
% 0.46/0.66          | ~ (l1_pre_topc @ X46)
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.46/0.66          | (v1_tsep_1 @ X45 @ X46)
% 0.46/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X45) @ X46)
% 0.46/0.66          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.46/0.66      inference('simplify', [status(thm)], ['96'])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      (((~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.46/0.66         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.46/0.66         | (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.46/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_B_2 @ sk_A)) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['66'])).
% 0.46/0.66  thf('112', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '41', '42', '43', '44'])).
% 0.46/0.66  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.66         | (v1_tsep_1 @ sk_B_2 @ sk_A))) <= (((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.46/0.66  thf('116', plain, (((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['4', '65'])).
% 0.46/0.66  thf('117', plain,
% 0.46/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.66        | (v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['93', '94'])).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      (![X45 : $i, X46 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X46)
% 0.46/0.66          | ~ (l1_pre_topc @ X46)
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X45) @ X46)
% 0.46/0.66          | ~ (v1_tsep_1 @ X45 @ X46)
% 0.46/0.66          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.46/0.66      inference('simplify', [status(thm)], ['82'])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      (((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.46/0.66         | ~ (v1_tsep_1 @ sk_C_1 @ sk_A)
% 0.46/0.66         | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)
% 0.46/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      (((m1_pre_topc @ sk_C_1 @ sk_A)) <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['5'])).
% 0.46/0.66  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      (((~ (v1_tsep_1 @ sk_C_1 @ sk_A)
% 0.46/0.66         | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)))
% 0.46/0.66         <= (((m1_pre_topc @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.46/0.66  thf('125', plain, (((m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['4', '65', '74'])).
% 0.46/0.66  thf('126', plain,
% 0.46/0.66      ((~ (v1_tsep_1 @ sk_C_1 @ sk_A)
% 0.46/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['124', '125'])).
% 0.46/0.66  thf('127', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_C_1 @ sk_A)) <= (((v1_tsep_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['75'])).
% 0.46/0.66  thf('128', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_C_1 @ sk_A)) | ((v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.46/0.66      inference('split', [status(esa)], ['75'])).
% 0.46/0.66  thf('129', plain, (((v1_tsep_1 @ sk_C_1 @ sk_A))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)],
% 0.46/0.66                ['2', '4', '65', '74', '105', '128'])).
% 0.46/0.66  thf('130', plain, ((v1_tsep_1 @ sk_C_1 @ sk_A)),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['127', '129'])).
% 0.46/0.66  thf('131', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['126', '130'])).
% 0.46/0.66  thf('132', plain, ((v1_tsep_1 @ sk_B_2 @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['117', '131'])).
% 0.46/0.66  thf('133', plain, ($false), inference('demod', [status(thm)], ['107', '132'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
