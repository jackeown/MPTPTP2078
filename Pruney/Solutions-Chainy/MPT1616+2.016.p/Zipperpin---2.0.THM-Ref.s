%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3psCxQDmro

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:21 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 125 expanded)
%              Number of leaves         :   45 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  639 (1010 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X41 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
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

thf('3',plain,(
    ! [X38: $i,X40: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( zip_tseitin_5 @ X40 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('4',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X41 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) )
      | ( zip_tseitin_4 @ X35 @ X36 )
      | ~ ( zip_tseitin_5 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( u1_pre_topc @ X33 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ ( u1_pre_topc @ X33 ) )
      | ~ ( zip_tseitin_4 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X41 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( r2_hidden @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('31',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X42 ) @ X42 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X42 ) )
        = ( k3_tarski @ X42 ) )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X42: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X42 ) )
        = ( k3_tarski @ X42 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X42 ) @ X42 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

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

thf('35',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('36',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('39',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('43',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3psCxQDmro
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 146 iterations in 0.092s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.36/0.55  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.36/0.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.36/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.36/0.55  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.36/0.55  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(dt_u1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( m1_subset_1 @
% 0.36/0.55         ( u1_pre_topc @ A ) @ 
% 0.36/0.55         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X41 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (u1_pre_topc @ X41) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41))))
% 0.36/0.55          | ~ (l1_pre_topc @ X41))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.55  thf(redefinition_k5_setfam_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.55       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.36/0.55              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf(d1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ( v2_pre_topc @ A ) <=>
% 0.36/0.55         ( ( ![B:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55               ( ![C:$i]:
% 0.36/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.36/0.55                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.36/0.55                     ( r2_hidden @
% 0.36/0.55                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.36/0.55                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.36/0.55           ( ![B:$i]:
% 0.36/0.55             ( ( m1_subset_1 @
% 0.36/0.55                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.36/0.55                 ( r2_hidden @
% 0.36/0.55                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.36/0.55                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.36/0.55           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_1, axiom,
% 0.36/0.55    (![B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.36/0.55       ( ( m1_subset_1 @
% 0.36/0.55           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.36/0.55  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_3, axiom,
% 0.36/0.55    (![B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.36/0.55       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.36/0.55         ( r2_hidden @
% 0.36/0.55           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_5, axiom,
% 0.36/0.55    (![B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.36/0.55       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_7, axiom,
% 0.36/0.55    (![C:$i,B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.36/0.55       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.36/0.55  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_9, axiom,
% 0.36/0.55    (![C:$i,B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.36/0.55       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.36/0.55         ( r2_hidden @
% 0.36/0.55           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_11, axiom,
% 0.36/0.55    (![C:$i,B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.36/0.55       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.36/0.55         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_12, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ( v2_pre_topc @ A ) <=>
% 0.36/0.55         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.36/0.55           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.36/0.55           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X38 : $i, X40 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X38)
% 0.36/0.55          | (zip_tseitin_5 @ X40 @ X38)
% 0.36/0.55          | ~ (l1_pre_topc @ X38))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X41 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (u1_pre_topc @ X41) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41))))
% 0.36/0.55          | ~ (l1_pre_topc @ X41))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X35 : $i, X36 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X35 @ 
% 0.36/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36))))
% 0.36/0.55          | (zip_tseitin_4 @ X35 @ X36)
% 0.36/0.55          | ~ (zip_tseitin_5 @ X35 @ X36))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 0.36/0.55          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('10', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.36/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X32 @ (u1_pre_topc @ X33))
% 0.36/0.55          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X33) @ X32) @ 
% 0.36/0.55             (u1_pre_topc @ X33))
% 0.36/0.55          | ~ (zip_tseitin_4 @ X32 @ X33))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.36/0.55          | (r2_hidden @ 
% 0.36/0.55             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.36/0.55             (u1_pre_topc @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (r2_hidden @ 
% 0.36/0.55             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.36/0.55             (u1_pre_topc @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['2', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X41 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (u1_pre_topc @ X41) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41))))
% 0.36/0.55          | ~ (l1_pre_topc @ X41))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.55  thf(t4_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X13 @ X14)
% 0.36/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.36/0.55          | (m1_subset_1 @ X13 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X38 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X38)
% 0.36/0.55          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.36/0.55          | ~ (l1_pre_topc @ X38))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.36/0.55  thf(l49_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X3 : $i, X5 : $i]:
% 0.36/0.55         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.36/0.55               (u1_struct_0 @ X0))
% 0.36/0.55          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.55  thf(t14_yellow_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.36/0.55         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X42 : $i]:
% 0.36/0.55         (~ (r2_hidden @ (k3_tarski @ X42) @ X42)
% 0.36/0.55          | ((k4_yellow_0 @ (k2_yellow_1 @ X42)) = (k3_tarski @ X42))
% 0.36/0.55          | (v1_xboole_0 @ X42))),
% 0.36/0.55      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.36/0.55  thf(d1_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X42 : $i]:
% 0.36/0.55         (((k4_yellow_0 @ (k2_yellow_1 @ X42)) = (k3_tarski @ X42))
% 0.36/0.55          | ~ (r2_hidden @ (k3_tarski @ X42) @ X42))),
% 0.36/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.36/0.55              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.36/0.55  thf(t24_yellow_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.36/0.55         ( u1_struct_0 @ A ) ) ))).
% 0.36/0.55  thf(zf_stmt_13, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.36/0.55            ( u1_struct_0 @ A ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.36/0.55         != (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.55  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.36/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '39'])).
% 0.36/0.55  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.36/0.55  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.36/0.55  thf('43', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.36/0.55  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
