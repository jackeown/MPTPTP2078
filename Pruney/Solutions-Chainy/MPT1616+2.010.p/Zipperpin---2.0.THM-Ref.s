%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0lhtABsHW3

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:21 EST 2020

% Result     : Theorem 6.44s
% Output     : Refutation 6.44s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 364 expanded)
%              Number of leaves         :   49 ( 134 expanded)
%              Depth                    :   20
%              Number of atoms          :  787 (3131 expanded)
%              Number of equality atoms :   27 ( 118 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X52: $i,X54: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ( zip_tseitin_5 @ X54 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X55 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('6',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ( zip_tseitin_4 @ X49 @ X50 )
      | ~ ( zip_tseitin_5 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X46 @ ( u1_pre_topc @ X47 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X47 ) @ X46 ) @ ( u1_pre_topc @ X47 ) )
      | ~ ( zip_tseitin_4 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X52: $i] :
      ( ~ ( v2_pre_topc @ X52 )
      | ( r2_hidden @ ( u1_struct_0 @ X52 ) @ ( u1_pre_topc @ X52 ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('17',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X30 @ X33 )
      | ~ ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ~ ( r2_hidden @ X30 @ ( u1_pre_topc @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X32 @ ( u1_pre_topc @ X31 ) )
      | ~ ( zip_tseitin_0 @ X32 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('24',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ ( k3_tarski @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('26',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X55 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        = ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X6 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ ( u1_pre_topc @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ ( k3_tarski @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( k2_xboole_0 @ ( u1_pre_topc @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( k2_xboole_0 @ ( u1_pre_topc @ sk_A ) @ X0 ) ) )
      = ( k3_tarski @ ( k2_xboole_0 @ ( u1_pre_topc @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( k3_tarski @ ( k2_xboole_0 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('43',plain,(
    ! [X18: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('44',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k3_tarski @ ( k2_xboole_0 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','47'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X16 ) @ X17 )
      | ( r2_hidden @ ( sk_C @ X17 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ ( k3_tarski @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X1 ) @ X2 )
      | ( r1_tarski @ ( sk_C @ X2 @ X1 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X16 ) @ X17 )
      | ~ ( r1_tarski @ ( sk_C @ X17 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X1 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_tarski @ X1 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ X1 ) @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','56'])).

thf('58',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','57'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('59',plain,(
    ! [X56: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X56 ) @ X56 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X56 ) )
        = ( k3_tarski @ X56 ) )
      | ( v1_xboole_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,(
    ! [X56: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X56 ) )
        = ( k3_tarski @ X56 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X56 ) @ X56 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('64',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','57'])).

thf('65',plain,
    ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0lhtABsHW3
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.44/6.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.44/6.67  % Solved by: fo/fo7.sh
% 6.44/6.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.44/6.67  % done 10270 iterations in 6.209s
% 6.44/6.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.44/6.67  % SZS output start Refutation
% 6.44/6.67  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 6.44/6.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.44/6.67  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 6.44/6.67  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 6.44/6.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.44/6.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.44/6.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.44/6.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.44/6.67  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.44/6.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.44/6.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.44/6.67  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 6.44/6.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.44/6.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.44/6.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 6.44/6.67  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 6.44/6.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.44/6.67  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 6.44/6.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.44/6.67  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 6.44/6.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.44/6.67  thf(sk_A_type, type, sk_A: $i).
% 6.44/6.67  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 6.44/6.67  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 6.44/6.67  thf(t24_yellow_1, conjecture,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.44/6.67       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 6.44/6.67         ( u1_struct_0 @ A ) ) ))).
% 6.44/6.67  thf(zf_stmt_0, negated_conjecture,
% 6.44/6.67    (~( ![A:$i]:
% 6.44/6.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.44/6.67            ( l1_pre_topc @ A ) ) =>
% 6.44/6.67          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 6.44/6.67            ( u1_struct_0 @ A ) ) ) )),
% 6.44/6.67    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 6.44/6.67  thf('0', plain, ((l1_pre_topc @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(d1_pre_topc, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( l1_pre_topc @ A ) =>
% 6.44/6.67       ( ( v2_pre_topc @ A ) <=>
% 6.44/6.67         ( ( ![B:$i]:
% 6.44/6.67             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.44/6.67               ( ![C:$i]:
% 6.44/6.67                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.44/6.67                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 6.44/6.67                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 6.44/6.67                     ( r2_hidden @
% 6.44/6.67                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 6.44/6.67                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 6.44/6.67           ( ![B:$i]:
% 6.44/6.67             ( ( m1_subset_1 @
% 6.44/6.67                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.44/6.67               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 6.44/6.67                 ( r2_hidden @
% 6.44/6.67                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 6.44/6.67                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 6.44/6.67           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_2, axiom,
% 6.44/6.67    (![B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_5 @ B @ A ) <=>
% 6.44/6.67       ( ( m1_subset_1 @
% 6.44/6.67           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.44/6.67         ( zip_tseitin_4 @ B @ A ) ) ))).
% 6.44/6.67  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_4, axiom,
% 6.44/6.67    (![B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_4 @ B @ A ) <=>
% 6.44/6.67       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 6.44/6.67         ( r2_hidden @
% 6.44/6.67           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_6, axiom,
% 6.44/6.67    (![B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_3 @ B @ A ) <=>
% 6.44/6.67       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.44/6.67         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_8, axiom,
% 6.44/6.67    (![C:$i,B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 6.44/6.67       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.44/6.67         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 6.44/6.67  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_10, axiom,
% 6.44/6.67    (![C:$i,B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 6.44/6.67       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 6.44/6.67         ( r2_hidden @
% 6.44/6.67           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_12, axiom,
% 6.44/6.67    (![C:$i,B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 6.44/6.67       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 6.44/6.67         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_13, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( l1_pre_topc @ A ) =>
% 6.44/6.67       ( ( v2_pre_topc @ A ) <=>
% 6.44/6.67         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 6.44/6.67           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 6.44/6.67           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 6.44/6.67  thf('1', plain,
% 6.44/6.67      (![X52 : $i, X54 : $i]:
% 6.44/6.67         (~ (v2_pre_topc @ X52)
% 6.44/6.67          | (zip_tseitin_5 @ X54 @ X52)
% 6.44/6.67          | ~ (l1_pre_topc @ X52))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_13])).
% 6.44/6.67  thf('2', plain,
% 6.44/6.67      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['0', '1'])).
% 6.44/6.67  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('4', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 6.44/6.67      inference('demod', [status(thm)], ['2', '3'])).
% 6.44/6.67  thf(dt_u1_pre_topc, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( l1_pre_topc @ A ) =>
% 6.44/6.67       ( m1_subset_1 @
% 6.44/6.67         ( u1_pre_topc @ A ) @ 
% 6.44/6.67         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 6.44/6.67  thf('5', plain,
% 6.44/6.67      (![X55 : $i]:
% 6.44/6.67         ((m1_subset_1 @ (u1_pre_topc @ X55) @ 
% 6.44/6.67           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55))))
% 6.44/6.67          | ~ (l1_pre_topc @ X55))),
% 6.44/6.67      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 6.44/6.67  thf('6', plain,
% 6.44/6.67      (![X49 : $i, X50 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X49 @ 
% 6.44/6.67             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 6.44/6.67          | (zip_tseitin_4 @ X49 @ X50)
% 6.44/6.67          | ~ (zip_tseitin_5 @ X49 @ X50))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.44/6.67  thf('7', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (l1_pre_topc @ X0)
% 6.44/6.67          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 6.44/6.67          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 6.44/6.67      inference('sup-', [status(thm)], ['5', '6'])).
% 6.44/6.67  thf('8', plain,
% 6.44/6.67      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['4', '7'])).
% 6.44/6.67  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('10', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 6.44/6.67      inference('demod', [status(thm)], ['8', '9'])).
% 6.44/6.67  thf(d10_xboole_0, axiom,
% 6.44/6.67    (![A:$i,B:$i]:
% 6.44/6.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.44/6.67  thf('11', plain,
% 6.44/6.67      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 6.44/6.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.44/6.67  thf('12', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 6.44/6.67      inference('simplify', [status(thm)], ['11'])).
% 6.44/6.67  thf('13', plain,
% 6.44/6.67      (![X46 : $i, X47 : $i]:
% 6.44/6.67         (~ (r1_tarski @ X46 @ (u1_pre_topc @ X47))
% 6.44/6.67          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X47) @ X46) @ 
% 6.44/6.67             (u1_pre_topc @ X47))
% 6.44/6.67          | ~ (zip_tseitin_4 @ X46 @ X47))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.44/6.67  thf('14', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 6.44/6.67          | (r2_hidden @ 
% 6.44/6.67             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 6.44/6.67             (u1_pre_topc @ X0)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['12', '13'])).
% 6.44/6.67  thf('15', plain,
% 6.44/6.67      ((r2_hidden @ 
% 6.44/6.67        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 6.44/6.67        (u1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['10', '14'])).
% 6.44/6.67  thf('16', plain,
% 6.44/6.67      (![X52 : $i]:
% 6.44/6.67         (~ (v2_pre_topc @ X52)
% 6.44/6.67          | (r2_hidden @ (u1_struct_0 @ X52) @ (u1_pre_topc @ X52))
% 6.44/6.67          | ~ (l1_pre_topc @ X52))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_13])).
% 6.44/6.67  thf('17', plain,
% 6.44/6.67      (![X30 : $i, X32 : $i, X33 : $i]:
% 6.44/6.67         ((zip_tseitin_0 @ X32 @ X30 @ X33)
% 6.44/6.67          | ~ (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 6.44/6.67          | ~ (r2_hidden @ X30 @ (u1_pre_topc @ X33)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_12])).
% 6.44/6.67  thf('18', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i]:
% 6.44/6.67         (~ (l1_pre_topc @ X0)
% 6.44/6.67          | ~ (v2_pre_topc @ X0)
% 6.44/6.67          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 6.44/6.67          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 6.44/6.67      inference('sup-', [status(thm)], ['16', '17'])).
% 6.44/6.67  thf('19', plain,
% 6.44/6.67      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 6.44/6.67         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 6.44/6.67        | ~ (v2_pre_topc @ sk_A)
% 6.44/6.67        | ~ (l1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['15', '18'])).
% 6.44/6.67  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('22', plain,
% 6.44/6.67      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 6.44/6.67        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 6.44/6.67      inference('demod', [status(thm)], ['19', '20', '21'])).
% 6.44/6.67  thf('23', plain,
% 6.44/6.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.44/6.67         ((r2_hidden @ X32 @ (u1_pre_topc @ X31))
% 6.44/6.67          | ~ (zip_tseitin_0 @ X32 @ X30 @ X31))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_12])).
% 6.44/6.67  thf('24', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['22', '23'])).
% 6.44/6.67  thf(l49_zfmisc_1, axiom,
% 6.44/6.67    (![A:$i,B:$i]:
% 6.44/6.67     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 6.44/6.67  thf('25', plain,
% 6.44/6.67      (![X14 : $i, X15 : $i]:
% 6.44/6.67         ((r1_tarski @ X14 @ (k3_tarski @ X15)) | ~ (r2_hidden @ X14 @ X15))),
% 6.44/6.67      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 6.44/6.67  thf('26', plain,
% 6.44/6.67      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['24', '25'])).
% 6.44/6.67  thf('27', plain,
% 6.44/6.67      (![X9 : $i, X11 : $i]:
% 6.44/6.67         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 6.44/6.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.44/6.67  thf('28', plain,
% 6.44/6.67      ((~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 6.44/6.67           (u1_struct_0 @ sk_A))
% 6.44/6.67        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['26', '27'])).
% 6.44/6.67  thf('29', plain,
% 6.44/6.67      (![X55 : $i]:
% 6.44/6.67         ((m1_subset_1 @ (u1_pre_topc @ X55) @ 
% 6.44/6.67           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55))))
% 6.44/6.67          | ~ (l1_pre_topc @ X55))),
% 6.44/6.67      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 6.44/6.67  thf(t3_subset, axiom,
% 6.44/6.67    (![A:$i,B:$i]:
% 6.44/6.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.44/6.67  thf('30', plain,
% 6.44/6.67      (![X22 : $i, X23 : $i]:
% 6.44/6.67         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 6.44/6.67      inference('cnf', [status(esa)], [t3_subset])).
% 6.44/6.67  thf('31', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (l1_pre_topc @ X0)
% 6.44/6.67          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 6.44/6.67             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['29', '30'])).
% 6.44/6.67  thf(t12_xboole_1, axiom,
% 6.44/6.67    (![A:$i,B:$i]:
% 6.44/6.67     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.44/6.67  thf('32', plain,
% 6.44/6.67      (![X12 : $i, X13 : $i]:
% 6.44/6.67         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 6.44/6.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.44/6.67  thf('33', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (l1_pre_topc @ X0)
% 6.44/6.67          | ((k2_xboole_0 @ (u1_pre_topc @ X0) @ 
% 6.44/6.67              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.44/6.67              = (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['31', '32'])).
% 6.44/6.67  thf('34', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['22', '23'])).
% 6.44/6.67  thf(d3_xboole_0, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 6.44/6.67       ( ![D:$i]:
% 6.44/6.67         ( ( r2_hidden @ D @ C ) <=>
% 6.44/6.67           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 6.44/6.67  thf('35', plain,
% 6.44/6.67      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 6.44/6.67         (~ (r2_hidden @ X3 @ X6)
% 6.44/6.67          | (r2_hidden @ X3 @ X5)
% 6.44/6.67          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 6.44/6.67      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.44/6.67  thf('36', plain,
% 6.44/6.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 6.44/6.67         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X6))),
% 6.44/6.67      inference('simplify', [status(thm)], ['35'])).
% 6.44/6.67  thf('37', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (r2_hidden @ (u1_struct_0 @ sk_A) @ 
% 6.44/6.67          (k2_xboole_0 @ (u1_pre_topc @ sk_A) @ X0))),
% 6.44/6.67      inference('sup-', [status(thm)], ['34', '36'])).
% 6.44/6.67  thf('38', plain,
% 6.44/6.67      (![X14 : $i, X15 : $i]:
% 6.44/6.67         ((r1_tarski @ X14 @ (k3_tarski @ X15)) | ~ (r2_hidden @ X14 @ X15))),
% 6.44/6.67      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 6.44/6.67  thf('39', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 6.44/6.67          (k3_tarski @ (k2_xboole_0 @ (u1_pre_topc @ sk_A) @ X0)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['37', '38'])).
% 6.44/6.67  thf('40', plain,
% 6.44/6.67      (![X12 : $i, X13 : $i]:
% 6.44/6.67         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 6.44/6.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.44/6.67  thf('41', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         ((k2_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 6.44/6.67           (k3_tarski @ (k2_xboole_0 @ (u1_pre_topc @ sk_A) @ X0)))
% 6.44/6.67           = (k3_tarski @ (k2_xboole_0 @ (u1_pre_topc @ sk_A) @ X0)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['39', '40'])).
% 6.44/6.67  thf('42', plain,
% 6.44/6.67      ((((k2_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 6.44/6.67          (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 6.44/6.67          = (k3_tarski @ 
% 6.44/6.67             (k2_xboole_0 @ (u1_pre_topc @ sk_A) @ 
% 6.44/6.67              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 6.44/6.67        | ~ (l1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup+', [status(thm)], ['33', '41'])).
% 6.44/6.67  thf(t99_zfmisc_1, axiom,
% 6.44/6.67    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 6.44/6.67  thf('43', plain, (![X18 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X18)) = (X18))),
% 6.44/6.67      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 6.44/6.67  thf('44', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 6.44/6.67      inference('simplify', [status(thm)], ['11'])).
% 6.44/6.67  thf('45', plain,
% 6.44/6.67      (![X12 : $i, X13 : $i]:
% 6.44/6.67         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 6.44/6.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.44/6.67  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 6.44/6.67      inference('sup-', [status(thm)], ['44', '45'])).
% 6.44/6.67  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('48', plain,
% 6.44/6.67      (((u1_struct_0 @ sk_A)
% 6.44/6.67         = (k3_tarski @ 
% 6.44/6.67            (k2_xboole_0 @ (u1_pre_topc @ sk_A) @ 
% 6.44/6.67             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 6.44/6.67      inference('demod', [status(thm)], ['42', '43', '46', '47'])).
% 6.44/6.67  thf(t94_zfmisc_1, axiom,
% 6.44/6.67    (![A:$i,B:$i]:
% 6.44/6.67     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 6.44/6.67       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 6.44/6.67  thf('49', plain,
% 6.44/6.67      (![X16 : $i, X17 : $i]:
% 6.44/6.67         ((r1_tarski @ (k3_tarski @ X16) @ X17)
% 6.44/6.67          | (r2_hidden @ (sk_C @ X17 @ X16) @ X16))),
% 6.44/6.67      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 6.44/6.67  thf('50', plain,
% 6.44/6.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 6.44/6.67         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X6))),
% 6.44/6.67      inference('simplify', [status(thm)], ['35'])).
% 6.44/6.67  thf('51', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.44/6.67         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 6.44/6.67          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['49', '50'])).
% 6.44/6.67  thf('52', plain,
% 6.44/6.67      (![X14 : $i, X15 : $i]:
% 6.44/6.67         ((r1_tarski @ X14 @ (k3_tarski @ X15)) | ~ (r2_hidden @ X14 @ X15))),
% 6.44/6.67      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 6.44/6.67  thf('53', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.44/6.67         ((r1_tarski @ (k3_tarski @ X1) @ X2)
% 6.44/6.67          | (r1_tarski @ (sk_C @ X2 @ X1) @ 
% 6.44/6.67             (k3_tarski @ (k2_xboole_0 @ X1 @ X0))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['51', '52'])).
% 6.44/6.67  thf('54', plain,
% 6.44/6.67      (![X16 : $i, X17 : $i]:
% 6.44/6.67         ((r1_tarski @ (k3_tarski @ X16) @ X17)
% 6.44/6.67          | ~ (r1_tarski @ (sk_C @ X17 @ X16) @ X17))),
% 6.44/6.67      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 6.44/6.67  thf('55', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i]:
% 6.44/6.67         ((r1_tarski @ (k3_tarski @ X1) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 6.44/6.67          | (r1_tarski @ (k3_tarski @ X1) @ 
% 6.44/6.67             (k3_tarski @ (k2_xboole_0 @ X1 @ X0))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['53', '54'])).
% 6.44/6.67  thf('56', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i]:
% 6.44/6.67         (r1_tarski @ (k3_tarski @ X1) @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))),
% 6.44/6.67      inference('simplify', [status(thm)], ['55'])).
% 6.44/6.67  thf('57', plain,
% 6.44/6.67      ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_struct_0 @ sk_A))),
% 6.44/6.67      inference('sup+', [status(thm)], ['48', '56'])).
% 6.44/6.67  thf('58', plain,
% 6.44/6.67      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['28', '57'])).
% 6.44/6.67  thf(t14_yellow_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.44/6.67       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 6.44/6.67         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 6.44/6.67  thf('59', plain,
% 6.44/6.67      (![X56 : $i]:
% 6.44/6.67         (~ (r2_hidden @ (k3_tarski @ X56) @ X56)
% 6.44/6.67          | ((k4_yellow_0 @ (k2_yellow_1 @ X56)) = (k3_tarski @ X56))
% 6.44/6.67          | (v1_xboole_0 @ X56))),
% 6.44/6.67      inference('cnf', [status(esa)], [t14_yellow_1])).
% 6.44/6.67  thf(d1_xboole_0, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.44/6.67  thf('60', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.44/6.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.44/6.67  thf('61', plain,
% 6.44/6.67      (![X56 : $i]:
% 6.44/6.67         (((k4_yellow_0 @ (k2_yellow_1 @ X56)) = (k3_tarski @ X56))
% 6.44/6.67          | ~ (r2_hidden @ (k3_tarski @ X56) @ X56))),
% 6.44/6.67      inference('clc', [status(thm)], ['59', '60'])).
% 6.44/6.67  thf('62', plain,
% 6.44/6.67      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 6.44/6.67        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 6.44/6.67            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['58', '61'])).
% 6.44/6.67  thf('63', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 6.44/6.67      inference('sup-', [status(thm)], ['22', '23'])).
% 6.44/6.67  thf('64', plain,
% 6.44/6.67      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['28', '57'])).
% 6.44/6.67  thf('65', plain,
% 6.44/6.67      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 6.44/6.67         = (u1_struct_0 @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['62', '63', '64'])).
% 6.44/6.67  thf('66', plain,
% 6.44/6.67      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 6.44/6.67         != (u1_struct_0 @ sk_A))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('67', plain, ($false),
% 6.44/6.67      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 6.44/6.67  
% 6.44/6.67  % SZS output end Refutation
% 6.44/6.67  
% 6.44/6.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
