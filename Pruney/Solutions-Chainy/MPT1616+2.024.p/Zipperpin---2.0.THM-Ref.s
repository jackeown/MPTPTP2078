%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AXDGtRpttf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:23 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 308 expanded)
%              Number of leaves         :   47 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          :  792 (2706 expanded)
%              Number of equality atoms :   19 (  80 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( zip_tseitin_3 @ X46 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( zip_tseitin_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_3 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( zip_tseitin_1 @ X31 @ X33 @ X32 )
      | ~ ( zip_tseitin_2 @ X31 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_2 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( r2_hidden @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('17',plain,(
    ! [X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( r2_hidden @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('18',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X23 @ X26 )
      | ~ ( r2_hidden @ X25 @ ( u1_pre_topc @ X26 ) )
      | ~ ( r2_hidden @ X23 @ ( u1_pre_topc @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ X27 ) @ ( u1_pre_topc @ X29 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( zip_tseitin_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('29',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X25 @ ( u1_pre_topc @ X24 ) )
      | ~ ( zip_tseitin_0 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('34',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X48 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('55',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X49: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 ) ) ),
    inference(clc,[status(thm)],['55','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('63',plain,
    ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AXDGtRpttf
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.27/2.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.27/2.48  % Solved by: fo/fo7.sh
% 2.27/2.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.27/2.48  % done 2311 iterations in 2.065s
% 2.27/2.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.27/2.48  % SZS output start Refutation
% 2.27/2.48  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 2.27/2.48  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 2.27/2.48  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 2.27/2.48  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 2.27/2.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.27/2.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.27/2.48  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 2.27/2.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.27/2.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.27/2.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.27/2.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.27/2.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 2.27/2.48  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 2.27/2.48  thf(sk_A_type, type, sk_A: $i).
% 2.27/2.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.27/2.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 2.27/2.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.27/2.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 2.27/2.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.27/2.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.27/2.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.27/2.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.27/2.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.27/2.48  thf(t24_yellow_1, conjecture,
% 2.27/2.48    (![A:$i]:
% 2.27/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.27/2.48       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 2.27/2.48         ( u1_struct_0 @ A ) ) ))).
% 2.27/2.48  thf(zf_stmt_0, negated_conjecture,
% 2.27/2.48    (~( ![A:$i]:
% 2.27/2.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.27/2.48            ( l1_pre_topc @ A ) ) =>
% 2.27/2.48          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 2.27/2.48            ( u1_struct_0 @ A ) ) ) )),
% 2.27/2.48    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 2.27/2.48  thf('0', plain, ((l1_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf(d1_pre_topc, axiom,
% 2.27/2.48    (![A:$i]:
% 2.27/2.48     ( ( l1_pre_topc @ A ) =>
% 2.27/2.48       ( ( v2_pre_topc @ A ) <=>
% 2.27/2.48         ( ( ![B:$i]:
% 2.27/2.48             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.27/2.48               ( ![C:$i]:
% 2.27/2.48                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.27/2.48                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 2.27/2.48                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 2.27/2.48                     ( r2_hidden @
% 2.27/2.48                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 2.27/2.48                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 2.27/2.48           ( ![B:$i]:
% 2.27/2.48             ( ( m1_subset_1 @
% 2.27/2.48                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.27/2.48               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.27/2.48                 ( r2_hidden @
% 2.27/2.48                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 2.27/2.48                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 2.27/2.48           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 2.27/2.48  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 2.27/2.48  thf(zf_stmt_2, axiom,
% 2.27/2.48    (![B:$i,A:$i]:
% 2.27/2.48     ( ( zip_tseitin_5 @ B @ A ) <=>
% 2.27/2.48       ( ( m1_subset_1 @
% 2.27/2.48           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.27/2.48         ( zip_tseitin_4 @ B @ A ) ) ))).
% 2.27/2.48  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 2.27/2.48  thf(zf_stmt_4, axiom,
% 2.27/2.48    (![B:$i,A:$i]:
% 2.27/2.48     ( ( zip_tseitin_4 @ B @ A ) <=>
% 2.27/2.48       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.27/2.48         ( r2_hidden @
% 2.27/2.48           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.27/2.48  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 2.27/2.48  thf(zf_stmt_6, axiom,
% 2.27/2.48    (![B:$i,A:$i]:
% 2.27/2.48     ( ( zip_tseitin_3 @ B @ A ) <=>
% 2.27/2.48       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.27/2.48         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 2.27/2.48  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 2.27/2.48  thf(zf_stmt_8, axiom,
% 2.27/2.48    (![C:$i,B:$i,A:$i]:
% 2.27/2.48     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 2.27/2.48       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.27/2.48         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 2.27/2.48  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.27/2.48  thf(zf_stmt_10, axiom,
% 2.27/2.48    (![C:$i,B:$i,A:$i]:
% 2.27/2.48     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 2.27/2.48       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 2.27/2.48         ( r2_hidden @
% 2.27/2.48           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.27/2.48  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 2.27/2.48  thf(zf_stmt_12, axiom,
% 2.27/2.48    (![C:$i,B:$i,A:$i]:
% 2.27/2.48     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 2.27/2.48       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 2.27/2.48         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 2.27/2.48  thf(zf_stmt_13, axiom,
% 2.27/2.48    (![A:$i]:
% 2.27/2.48     ( ( l1_pre_topc @ A ) =>
% 2.27/2.48       ( ( v2_pre_topc @ A ) <=>
% 2.27/2.48         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 2.27/2.48           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 2.27/2.48           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 2.27/2.48  thf('1', plain,
% 2.27/2.48      (![X45 : $i, X46 : $i]:
% 2.27/2.48         (~ (v2_pre_topc @ X45)
% 2.27/2.48          | (zip_tseitin_3 @ X46 @ X45)
% 2.27/2.48          | ~ (l1_pre_topc @ X45))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.27/2.48  thf('2', plain,
% 2.27/2.48      (![X0 : $i]: ((zip_tseitin_3 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 2.27/2.48      inference('sup-', [status(thm)], ['0', '1'])).
% 2.27/2.48  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('4', plain, (![X0 : $i]: (zip_tseitin_3 @ X0 @ sk_A)),
% 2.27/2.48      inference('demod', [status(thm)], ['2', '3'])).
% 2.27/2.48  thf(d10_xboole_0, axiom,
% 2.27/2.48    (![A:$i,B:$i]:
% 2.27/2.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.27/2.48  thf('5', plain,
% 2.27/2.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.27/2.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.48  thf('6', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.27/2.48      inference('simplify', [status(thm)], ['5'])).
% 2.27/2.48  thf(t3_subset, axiom,
% 2.27/2.48    (![A:$i,B:$i]:
% 2.27/2.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.27/2.48  thf('7', plain,
% 2.27/2.48      (![X17 : $i, X19 : $i]:
% 2.27/2.48         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 2.27/2.48      inference('cnf', [status(esa)], [t3_subset])).
% 2.27/2.48  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['6', '7'])).
% 2.27/2.48  thf('9', plain,
% 2.27/2.48      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.27/2.48         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 2.27/2.48          | (zip_tseitin_2 @ X37 @ X35 @ X36)
% 2.27/2.48          | ~ (zip_tseitin_3 @ X35 @ X36))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_6])).
% 2.27/2.48  thf('10', plain,
% 2.27/2.48      (![X0 : $i, X1 : $i]:
% 2.27/2.48         (~ (zip_tseitin_3 @ (u1_struct_0 @ X0) @ X0)
% 2.27/2.48          | (zip_tseitin_2 @ X1 @ (u1_struct_0 @ X0) @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['8', '9'])).
% 2.27/2.48  thf('11', plain,
% 2.27/2.48      (![X0 : $i]: (zip_tseitin_2 @ X0 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 2.27/2.48      inference('sup-', [status(thm)], ['4', '10'])).
% 2.27/2.48  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['6', '7'])).
% 2.27/2.48  thf('13', plain,
% 2.27/2.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.27/2.48         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 2.27/2.48          | (zip_tseitin_1 @ X31 @ X33 @ X32)
% 2.27/2.48          | ~ (zip_tseitin_2 @ X31 @ X33 @ X32))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_8])).
% 2.27/2.48  thf('14', plain,
% 2.27/2.48      (![X0 : $i, X1 : $i]:
% 2.27/2.48         (~ (zip_tseitin_2 @ (u1_struct_0 @ X0) @ X1 @ X0)
% 2.27/2.48          | (zip_tseitin_1 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['12', '13'])).
% 2.27/2.48  thf('15', plain,
% 2.27/2.48      ((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_A)),
% 2.27/2.48      inference('sup-', [status(thm)], ['11', '14'])).
% 2.27/2.48  thf('16', plain,
% 2.27/2.48      (![X45 : $i]:
% 2.27/2.48         (~ (v2_pre_topc @ X45)
% 2.27/2.48          | (r2_hidden @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45))
% 2.27/2.48          | ~ (l1_pre_topc @ X45))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.27/2.48  thf('17', plain,
% 2.27/2.48      (![X45 : $i]:
% 2.27/2.48         (~ (v2_pre_topc @ X45)
% 2.27/2.48          | (r2_hidden @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45))
% 2.27/2.48          | ~ (l1_pre_topc @ X45))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.27/2.48  thf('18', plain,
% 2.27/2.48      (![X23 : $i, X25 : $i, X26 : $i]:
% 2.27/2.48         ((zip_tseitin_0 @ X25 @ X23 @ X26)
% 2.27/2.48          | ~ (r2_hidden @ X25 @ (u1_pre_topc @ X26))
% 2.27/2.48          | ~ (r2_hidden @ X23 @ (u1_pre_topc @ X26)))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.27/2.48  thf('19', plain,
% 2.27/2.48      (![X0 : $i, X1 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | ~ (v2_pre_topc @ X0)
% 2.27/2.48          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 2.27/2.48          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['17', '18'])).
% 2.27/2.48  thf('20', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | ~ (v2_pre_topc @ X0)
% 2.27/2.48          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)
% 2.27/2.48          | ~ (v2_pre_topc @ X0)
% 2.27/2.48          | ~ (l1_pre_topc @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['16', '19'])).
% 2.27/2.48  thf('21', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         ((zip_tseitin_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)
% 2.27/2.48          | ~ (v2_pre_topc @ X0)
% 2.27/2.48          | ~ (l1_pre_topc @ X0))),
% 2.27/2.48      inference('simplify', [status(thm)], ['20'])).
% 2.27/2.48  thf('22', plain,
% 2.27/2.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.27/2.48         (~ (zip_tseitin_0 @ X27 @ X28 @ X29)
% 2.27/2.48          | (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ X29) @ X28 @ X27) @ 
% 2.27/2.48             (u1_pre_topc @ X29))
% 2.27/2.48          | ~ (zip_tseitin_1 @ X27 @ X28 @ X29))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_10])).
% 2.27/2.48  thf('23', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | ~ (v2_pre_topc @ X0)
% 2.27/2.48          | ~ (zip_tseitin_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)
% 2.27/2.48          | (r2_hidden @ 
% 2.27/2.48             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.27/2.48              (u1_struct_0 @ X0)) @ 
% 2.27/2.48             (u1_pre_topc @ X0)))),
% 2.27/2.48      inference('sup-', [status(thm)], ['21', '22'])).
% 2.27/2.48  thf('24', plain,
% 2.27/2.48      (((r2_hidden @ 
% 2.27/2.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48          (u1_struct_0 @ sk_A)) @ 
% 2.27/2.48         (u1_pre_topc @ sk_A))
% 2.27/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.27/2.48        | ~ (l1_pre_topc @ sk_A))),
% 2.27/2.48      inference('sup-', [status(thm)], ['15', '23'])).
% 2.27/2.48  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('27', plain,
% 2.27/2.48      ((r2_hidden @ 
% 2.27/2.48        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48         (u1_struct_0 @ sk_A)) @ 
% 2.27/2.48        (u1_pre_topc @ sk_A))),
% 2.27/2.48      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.27/2.48  thf('28', plain,
% 2.27/2.48      (![X0 : $i, X1 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | ~ (v2_pre_topc @ X0)
% 2.27/2.48          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 2.27/2.48          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['17', '18'])).
% 2.27/2.48  thf('29', plain,
% 2.27/2.48      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48          (u1_struct_0 @ sk_A)) @ 
% 2.27/2.48         sk_A)
% 2.27/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.27/2.48        | ~ (l1_pre_topc @ sk_A))),
% 2.27/2.48      inference('sup-', [status(thm)], ['27', '28'])).
% 2.27/2.48  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('32', plain,
% 2.27/2.48      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48         (u1_struct_0 @ sk_A)) @ 
% 2.27/2.48        sk_A)),
% 2.27/2.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 2.27/2.48  thf('33', plain,
% 2.27/2.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.27/2.48         ((r2_hidden @ X25 @ (u1_pre_topc @ X24))
% 2.27/2.48          | ~ (zip_tseitin_0 @ X25 @ X23 @ X24))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_12])).
% 2.27/2.48  thf('34', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 2.27/2.48      inference('sup-', [status(thm)], ['32', '33'])).
% 2.27/2.48  thf(d3_tarski, axiom,
% 2.27/2.48    (![A:$i,B:$i]:
% 2.27/2.48     ( ( r1_tarski @ A @ B ) <=>
% 2.27/2.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.27/2.48  thf('35', plain,
% 2.27/2.48      (![X1 : $i, X3 : $i]:
% 2.27/2.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.27/2.48      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.48  thf(d4_tarski, axiom,
% 2.27/2.48    (![A:$i,B:$i]:
% 2.27/2.48     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 2.27/2.48       ( ![C:$i]:
% 2.27/2.48         ( ( r2_hidden @ C @ B ) <=>
% 2.27/2.48           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 2.27/2.48  thf('36', plain,
% 2.27/2.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.27/2.48         (~ (r2_hidden @ X7 @ X8)
% 2.27/2.48          | ~ (r2_hidden @ X9 @ X7)
% 2.27/2.48          | (r2_hidden @ X9 @ X10)
% 2.27/2.48          | ((X10) != (k3_tarski @ X8)))),
% 2.27/2.48      inference('cnf', [status(esa)], [d4_tarski])).
% 2.27/2.48  thf('37', plain,
% 2.27/2.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.27/2.48         ((r2_hidden @ X9 @ (k3_tarski @ X8))
% 2.27/2.48          | ~ (r2_hidden @ X9 @ X7)
% 2.27/2.48          | ~ (r2_hidden @ X7 @ X8))),
% 2.27/2.48      inference('simplify', [status(thm)], ['36'])).
% 2.27/2.48  thf('38', plain,
% 2.27/2.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.27/2.48         ((r1_tarski @ X0 @ X1)
% 2.27/2.48          | ~ (r2_hidden @ X0 @ X2)
% 2.27/2.48          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 2.27/2.48      inference('sup-', [status(thm)], ['35', '37'])).
% 2.27/2.48  thf('39', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         ((r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 2.27/2.48           (k3_tarski @ (u1_pre_topc @ sk_A)))
% 2.27/2.48          | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['34', '38'])).
% 2.27/2.48  thf('40', plain,
% 2.27/2.48      (![X1 : $i, X3 : $i]:
% 2.27/2.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.27/2.48      inference('cnf', [status(esa)], [d3_tarski])).
% 2.27/2.48  thf('41', plain,
% 2.27/2.48      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))
% 2.27/2.48        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 2.27/2.48           (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 2.27/2.48      inference('sup-', [status(thm)], ['39', '40'])).
% 2.27/2.48  thf('42', plain,
% 2.27/2.48      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 2.27/2.48      inference('simplify', [status(thm)], ['41'])).
% 2.27/2.48  thf(dt_u1_pre_topc, axiom,
% 2.27/2.48    (![A:$i]:
% 2.27/2.48     ( ( l1_pre_topc @ A ) =>
% 2.27/2.48       ( m1_subset_1 @
% 2.27/2.48         ( u1_pre_topc @ A ) @ 
% 2.27/2.48         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 2.27/2.48  thf('43', plain,
% 2.27/2.48      (![X48 : $i]:
% 2.27/2.48         ((m1_subset_1 @ (u1_pre_topc @ X48) @ 
% 2.27/2.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 2.27/2.48          | ~ (l1_pre_topc @ X48))),
% 2.27/2.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 2.27/2.48  thf('44', plain,
% 2.27/2.48      (![X17 : $i, X18 : $i]:
% 2.27/2.48         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 2.27/2.48      inference('cnf', [status(esa)], [t3_subset])).
% 2.27/2.48  thf('45', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 2.27/2.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.27/2.48      inference('sup-', [status(thm)], ['43', '44'])).
% 2.27/2.48  thf(t95_zfmisc_1, axiom,
% 2.27/2.48    (![A:$i,B:$i]:
% 2.27/2.48     ( ( r1_tarski @ A @ B ) =>
% 2.27/2.48       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 2.27/2.48  thf('46', plain,
% 2.27/2.48      (![X14 : $i, X15 : $i]:
% 2.27/2.48         ((r1_tarski @ (k3_tarski @ X14) @ (k3_tarski @ X15))
% 2.27/2.48          | ~ (r1_tarski @ X14 @ X15))),
% 2.27/2.48      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 2.27/2.48  thf('47', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 2.27/2.48             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 2.27/2.48      inference('sup-', [status(thm)], ['45', '46'])).
% 2.27/2.48  thf(t99_zfmisc_1, axiom,
% 2.27/2.48    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 2.27/2.48  thf('48', plain, (![X16 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X16)) = (X16))),
% 2.27/2.48      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 2.27/2.48  thf('49', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 2.27/2.48      inference('demod', [status(thm)], ['47', '48'])).
% 2.27/2.48  thf('50', plain,
% 2.27/2.48      (![X4 : $i, X6 : $i]:
% 2.27/2.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.27/2.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.27/2.48  thf('51', plain,
% 2.27/2.48      (![X0 : $i]:
% 2.27/2.48         (~ (l1_pre_topc @ X0)
% 2.27/2.48          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.27/2.48               (k3_tarski @ (u1_pre_topc @ X0)))
% 2.27/2.48          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0))))),
% 2.27/2.48      inference('sup-', [status(thm)], ['49', '50'])).
% 2.27/2.48  thf('52', plain,
% 2.27/2.48      ((((u1_struct_0 @ sk_A) = (k3_tarski @ (u1_pre_topc @ sk_A)))
% 2.27/2.48        | ~ (l1_pre_topc @ sk_A))),
% 2.27/2.48      inference('sup-', [status(thm)], ['42', '51'])).
% 2.27/2.48  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('54', plain,
% 2.27/2.48      (((u1_struct_0 @ sk_A) = (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 2.27/2.48      inference('demod', [status(thm)], ['52', '53'])).
% 2.27/2.48  thf(t14_yellow_1, axiom,
% 2.27/2.48    (![A:$i]:
% 2.27/2.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.27/2.48       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 2.27/2.48         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 2.27/2.48  thf('55', plain,
% 2.27/2.48      (![X49 : $i]:
% 2.27/2.48         (~ (r2_hidden @ (k3_tarski @ X49) @ X49)
% 2.27/2.48          | ((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 2.27/2.48          | (v1_xboole_0 @ X49))),
% 2.27/2.48      inference('cnf', [status(esa)], [t14_yellow_1])).
% 2.27/2.48  thf('56', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['6', '7'])).
% 2.27/2.48  thf(t5_subset, axiom,
% 2.27/2.48    (![A:$i,B:$i,C:$i]:
% 2.27/2.48     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.27/2.48          ( v1_xboole_0 @ C ) ) ))).
% 2.27/2.48  thf('57', plain,
% 2.27/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.27/2.48         (~ (r2_hidden @ X20 @ X21)
% 2.27/2.48          | ~ (v1_xboole_0 @ X22)
% 2.27/2.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 2.27/2.48      inference('cnf', [status(esa)], [t5_subset])).
% 2.27/2.48  thf('58', plain,
% 2.27/2.48      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.27/2.48      inference('sup-', [status(thm)], ['56', '57'])).
% 2.27/2.48  thf('59', plain,
% 2.27/2.48      (![X49 : $i]:
% 2.27/2.48         (((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 2.27/2.48          | ~ (r2_hidden @ (k3_tarski @ X49) @ X49))),
% 2.27/2.48      inference('clc', [status(thm)], ['55', '58'])).
% 2.27/2.48  thf('60', plain,
% 2.27/2.48      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 2.27/2.48        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 2.27/2.48            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 2.27/2.48      inference('sup-', [status(thm)], ['54', '59'])).
% 2.27/2.48  thf('61', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 2.27/2.48      inference('sup-', [status(thm)], ['32', '33'])).
% 2.27/2.48  thf('62', plain,
% 2.27/2.48      (((u1_struct_0 @ sk_A) = (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 2.27/2.48      inference('demod', [status(thm)], ['52', '53'])).
% 2.27/2.48  thf('63', plain,
% 2.27/2.48      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 2.27/2.48         = (u1_struct_0 @ sk_A))),
% 2.27/2.48      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.27/2.48  thf('64', plain,
% 2.27/2.48      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 2.27/2.48         != (u1_struct_0 @ sk_A))),
% 2.27/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.27/2.48  thf('65', plain, ($false),
% 2.27/2.48      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 2.27/2.48  
% 2.27/2.48  % SZS output end Refutation
% 2.27/2.48  
% 2.27/2.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
