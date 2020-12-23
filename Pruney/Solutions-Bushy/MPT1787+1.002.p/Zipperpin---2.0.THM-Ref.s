%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1787+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uu3SK2HZLm

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:14 EST 2020

% Result     : Theorem 22.63s
% Output     : Refutation 22.70s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 474 expanded)
%              Number of leaves         :   55 ( 168 expanded)
%              Depth                    :   21
%              Number of atoms          : 1484 (4888 expanded)
%              Number of equality atoms :   42 ( 101 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(a_2_0_tmap_1_type,type,(
    a_2_0_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t102_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t102_tmap_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B_3 @ ( k5_tmap_1 @ sk_A @ sk_B_3 ) ) ),
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

thf('1',plain,(
    ! [X29: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ( r2_hidden @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X37 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('3',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) )
      | ( m1_subset_1 @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('8',plain,(
    ! [X60: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X60 ) )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k9_subset_1 @ X49 @ X47 @ X48 )
        = ( k3_xboole_0 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X53: $i] :
      ( ( k3_xboole_0 @ X53 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_3 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(fraenkel_a_2_0_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_tmap_1 @ B @ C ) )
      <=> ? [D: $i,E: $i] :
            ( ( r2_hidden @ E @ ( u1_pre_topc @ B ) )
            & ( r2_hidden @ D @ ( u1_pre_topc @ B ) )
            & ( A
              = ( k4_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k9_subset_1 @ ( u1_struct_0 @ B ) @ E @ C ) ) )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( r2_hidden @ X41 @ ( a_2_0_tmap_1 @ X39 @ X40 ) )
      | ~ ( r2_hidden @ X42 @ ( u1_pre_topc @ X39 ) )
      | ( X41
       != ( k4_subset_1 @ ( u1_struct_0 @ X39 ) @ X43 @ ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X42 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( r2_hidden @ X43 @ ( u1_pre_topc @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_tmap_1])).

thf('28',plain,(
    ! [X39: $i,X40: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ ( u1_pre_topc @ X39 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( r2_hidden @ X42 @ ( u1_pre_topc @ X39 ) )
      | ( r2_hidden @ ( k4_subset_1 @ ( u1_struct_0 @ X39 ) @ X43 @ ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X42 @ X40 ) ) @ ( a_2_0_tmap_1 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) ) @ ( a_2_0_tmap_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) ) @ ( a_2_0_tmap_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X60: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X60 ) )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X14 )
      | ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X12 @ X11 ) @ ( u1_pre_topc @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X15 @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( zip_tseitin_1 @ X15 @ X17 @ X16 )
      | ~ ( zip_tseitin_2 @ X15 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ sk_A )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X29: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ( r2_hidden @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('49',plain,(
    ! [X60: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X60 ) )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf('50',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X7 @ X10 )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ X11 ) @ ( u1_pre_topc @ X13 ) )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('58',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k9_subset_1 @ X49 @ X47 @ X48 )
        = ( k3_xboole_0 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X53: $i] :
      ( ( k3_xboole_0 @ X53 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['56','61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) ) @ ( a_2_0_tmap_1 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_3 ) ) @ ( a_2_0_tmap_1 @ sk_A @ sk_B_3 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k9_subset_1 @ X49 @ X47 @ X48 )
        = ( k3_xboole_0 @ X47 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_3 )
      = ( k3_xboole_0 @ X0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_3 )
      = ( k3_xboole_0 @ X0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B_3 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k4_subset_1 @ X45 @ X44 @ X46 )
        = ( k2_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('80',plain,(
    ! [X50: $i] :
      ( ( k2_xboole_0 @ X50 @ k1_xboole_0 )
      = X50 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B_3 @ X0 ) )
        = ( k3_xboole_0 @ sk_B_3 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B_3 @ X0 ) )
      = ( k3_xboole_0 @ sk_B_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B_3 ) )
      = ( k3_xboole_0 @ sk_B_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k5_tmap_1 @ A @ B )
            = ( a_2_0_tmap_1 @ A @ B ) ) ) ) )).

thf('89',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k5_tmap_1 @ X33 @ X32 )
        = ( a_2_0_tmap_1 @ X33 @ X32 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d8_tmap_1])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k5_tmap_1 @ sk_A @ sk_B_3 )
      = ( a_2_0_tmap_1 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k5_tmap_1 @ sk_A @ sk_B_3 )
      = ( a_2_0_tmap_1 @ sk_A @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k5_tmap_1 @ sk_A @ sk_B_3 )
    = ( a_2_0_tmap_1 @ sk_A @ sk_B_3 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ ( k3_xboole_0 @ sk_B_3 @ X0 ) @ ( k5_tmap_1 @ sk_A @ sk_B_3 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','69','87','95'])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) @ ( k5_tmap_1 @ sk_A @ sk_B_3 ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('101',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,(
    r1_tarski @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('103',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X51 @ X52 )
        = X51 )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_3 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['56','61','62','63'])).

thf('106',plain,(
    ! [X29: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ( r2_hidden @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('107',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X7 @ X10 )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( u1_pre_topc @ X8 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('114',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_3 @ ( k5_tmap_1 @ sk_A @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['97','98','99','104','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r2_hidden @ sk_B_3 @ ( k5_tmap_1 @ sk_A @ sk_B_3 ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).


%------------------------------------------------------------------------------
