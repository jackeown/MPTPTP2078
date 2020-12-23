%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NuDIRDvGpq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:51 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  182 (2404 expanded)
%              Number of leaves         :   40 ( 726 expanded)
%              Depth                    :   29
%              Number of atoms          : 1443 (25968 expanded)
%              Number of equality atoms :   47 ( 688 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X30 @ X31 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( X34
       != ( u1_struct_0 @ X32 ) )
      | ~ ( v1_tdlat_3 @ X32 )
      | ( v2_tex_2 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X32 ) @ X33 )
      | ~ ( v1_tdlat_3 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X30 @ X31 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X30
        = ( u1_struct_0 @ ( sk_C_1 @ X30 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('46',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X11 @ X13 @ X12 )
        = ( k9_subset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_pre_topc @ X36 @ ( sk_C_2 @ X35 @ X36 ) ) )
       != ( sk_C_2 @ X35 @ X36 ) )
      | ( v2_tex_2 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_B )
     != ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( sk_C_2 @ sk_B @ sk_A ) ) )
     != ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( sk_C_2 @ sk_B @ sk_A ) ) )
     != ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( sk_C_2 @ sk_B @ sk_A ) ) )
 != ( sk_C_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B
     != ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( r1_tarski @ ( sk_C_2 @ X35 @ X36 ) @ X35 )
      | ( v2_tex_2 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r1_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('82',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( sk_C_2 @ sk_B @ sk_A )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['70','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['42','85'])).

thf('87',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
      | ( X0
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( X0
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','90'])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['70','84'])).

thf('96',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','96','97'])).

thf('99',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['70','84'])).

thf('103',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v1_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_tdlat_3 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('113',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('114',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['70','84'])).

thf('119',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','103','119','120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('123',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X30 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('124',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('128',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('129',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['70','84'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['70','84'])).

thf('139',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NuDIRDvGpq
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:16:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.84/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.02  % Solved by: fo/fo7.sh
% 0.84/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.02  % done 746 iterations in 0.561s
% 0.84/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.02  % SZS output start Refutation
% 0.84/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.02  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.84/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.02  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.84/1.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.02  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.84/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.02  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.84/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.02  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.84/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.02  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.84/1.02  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.84/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.02  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.84/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.02  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.84/1.02  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.84/1.02  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.84/1.02  thf(t43_tex_2, conjecture,
% 0.84/1.02    (![A:$i]:
% 0.84/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.84/1.02         ( l1_pre_topc @ A ) ) =>
% 0.84/1.02       ( ![B:$i]:
% 0.84/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.02           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.84/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.02    (~( ![A:$i]:
% 0.84/1.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.84/1.02            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.02          ( ![B:$i]:
% 0.84/1.02            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.02              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.84/1.02    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.84/1.02  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('1', plain,
% 0.84/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf(t10_tsep_1, axiom,
% 0.84/1.02    (![A:$i]:
% 0.84/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.02       ( ![B:$i]:
% 0.84/1.02         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.84/1.02             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.02           ( ?[C:$i]:
% 0.84/1.02             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.84/1.02               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.84/1.02  thf('2', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((v1_xboole_0 @ X30)
% 0.84/1.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.84/1.02          | (m1_pre_topc @ (sk_C_1 @ X30 @ X31) @ X31)
% 0.84/1.02          | ~ (l1_pre_topc @ X31)
% 0.84/1.02          | (v2_struct_0 @ X31))),
% 0.84/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.84/1.02  thf('3', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.02  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('5', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('demod', [status(thm)], ['3', '4'])).
% 0.84/1.02  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('7', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['5', '6'])).
% 0.84/1.02  thf(t1_tsep_1, axiom,
% 0.84/1.02    (![A:$i]:
% 0.84/1.02     ( ( l1_pre_topc @ A ) =>
% 0.84/1.02       ( ![B:$i]:
% 0.84/1.02         ( ( m1_pre_topc @ B @ A ) =>
% 0.84/1.02           ( m1_subset_1 @
% 0.84/1.02             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.84/1.02  thf('8', plain,
% 0.84/1.02      (![X25 : $i, X26 : $i]:
% 0.84/1.02         (~ (m1_pre_topc @ X25 @ X26)
% 0.84/1.02          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.84/1.02             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.84/1.02          | ~ (l1_pre_topc @ X26))),
% 0.84/1.02      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.84/1.02  thf('9', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.02  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('11', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.02  thf(t26_tex_2, axiom,
% 0.84/1.02    (![A:$i]:
% 0.84/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.02       ( ![B:$i]:
% 0.84/1.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.84/1.02           ( ![C:$i]:
% 0.84/1.02             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.02               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.84/1.02                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.84/1.02  thf('12', plain,
% 0.84/1.02      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.84/1.02         ((v2_struct_0 @ X32)
% 0.84/1.02          | ~ (m1_pre_topc @ X32 @ X33)
% 0.84/1.02          | ((X34) != (u1_struct_0 @ X32))
% 0.84/1.02          | ~ (v1_tdlat_3 @ X32)
% 0.84/1.02          | (v2_tex_2 @ X34 @ X33)
% 0.84/1.02          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.84/1.02          | ~ (l1_pre_topc @ X33)
% 0.84/1.02          | (v2_struct_0 @ X33))),
% 0.84/1.02      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.84/1.02  thf('13', plain,
% 0.84/1.02      (![X32 : $i, X33 : $i]:
% 0.84/1.02         ((v2_struct_0 @ X33)
% 0.84/1.02          | ~ (l1_pre_topc @ X33)
% 0.84/1.02          | ~ (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.84/1.02               (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.84/1.02          | (v2_tex_2 @ (u1_struct_0 @ X32) @ X33)
% 0.84/1.02          | ~ (v1_tdlat_3 @ X32)
% 0.84/1.02          | ~ (m1_pre_topc @ X32 @ X33)
% 0.84/1.02          | (v2_struct_0 @ X32))),
% 0.84/1.02      inference('simplify', [status(thm)], ['12'])).
% 0.84/1.02  thf('14', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.84/1.02        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (v2_struct_0 @ sk_A))),
% 0.84/1.02      inference('sup-', [status(thm)], ['11', '13'])).
% 0.84/1.02  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('16', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.84/1.02        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 0.84/1.02        | (v2_struct_0 @ sk_A))),
% 0.84/1.02      inference('demod', [status(thm)], ['14', '15'])).
% 0.84/1.02  thf('17', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.02  thf('18', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((v1_xboole_0 @ X30)
% 0.84/1.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.84/1.02          | (m1_pre_topc @ (sk_C_1 @ X30 @ X31) @ X31)
% 0.84/1.02          | ~ (l1_pre_topc @ X31)
% 0.84/1.02          | (v2_struct_0 @ X31))),
% 0.84/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.84/1.02  thf('19', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (m1_pre_topc @ 
% 0.84/1.02           (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A) @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.02  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('21', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (m1_pre_topc @ 
% 0.84/1.02           (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A) @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['19', '20'])).
% 0.84/1.02  thf(d10_xboole_0, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.02  thf('22', plain,
% 0.84/1.02      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.84/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.02  thf('23', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.84/1.02      inference('simplify', [status(thm)], ['22'])).
% 0.84/1.02  thf('24', plain,
% 0.84/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('25', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((v1_xboole_0 @ X30)
% 0.84/1.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.84/1.02          | ((X30) = (u1_struct_0 @ (sk_C_1 @ X30 @ X31)))
% 0.84/1.02          | ~ (l1_pre_topc @ X31)
% 0.84/1.02          | (v2_struct_0 @ X31))),
% 0.84/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.84/1.02  thf('26', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['24', '25'])).
% 0.84/1.02  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('28', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.02  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('30', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('clc', [status(thm)], ['28', '29'])).
% 0.84/1.02  thf('31', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('clc', [status(thm)], ['28', '29'])).
% 0.84/1.02  thf(d3_tarski, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.02  thf('32', plain,
% 0.84/1.02      (![X3 : $i, X5 : $i]:
% 0.84/1.02         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.84/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.02  thf('33', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.02  thf(t3_subset, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.02  thf('34', plain,
% 0.84/1.02      (![X19 : $i, X20 : $i]:
% 0.84/1.02         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.02  thf('35', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (r1_tarski @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.02  thf('36', plain,
% 0.84/1.02      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X2 @ X3)
% 0.84/1.02          | (r2_hidden @ X2 @ X4)
% 0.84/1.02          | ~ (r1_tarski @ X3 @ X4))),
% 0.84/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.02  thf('37', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((v1_xboole_0 @ sk_B)
% 0.84/1.02          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.84/1.02          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.02  thf('38', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((r1_tarski @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ X0)
% 0.84/1.02          | (r2_hidden @ 
% 0.84/1.02             (sk_C @ X0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))) @ 
% 0.84/1.02             (u1_struct_0 @ sk_A))
% 0.84/1.02          | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['32', '37'])).
% 0.84/1.02  thf('39', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.84/1.02          | (v1_xboole_0 @ sk_B)
% 0.84/1.02          | (v1_xboole_0 @ sk_B)
% 0.84/1.02          | (r1_tarski @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ X0))),
% 0.84/1.02      inference('sup+', [status(thm)], ['31', '38'])).
% 0.84/1.02  thf('40', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((r1_tarski @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ X0)
% 0.84/1.02          | (v1_xboole_0 @ sk_B)
% 0.84/1.02          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('simplify', [status(thm)], ['39'])).
% 0.84/1.02  thf('41', plain,
% 0.84/1.02      (![X19 : $i, X21 : $i]:
% 0.84/1.02         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.84/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.02  thf('42', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.84/1.02          | (v1_xboole_0 @ sk_B)
% 0.84/1.02          | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02             (k1_zfmisc_1 @ X0)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.02  thf('43', plain,
% 0.84/1.02      (![X3 : $i, X5 : $i]:
% 0.84/1.02         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.84/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.02  thf(dt_k2_subset_1, axiom,
% 0.84/1.02    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.84/1.02  thf('44', plain,
% 0.84/1.02      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.84/1.02      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.84/1.02  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.84/1.02  thf('45', plain, (![X14 : $i]: ((k2_subset_1 @ X14) = (X14))),
% 0.84/1.02      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.84/1.02  thf('46', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.84/1.02      inference('demod', [status(thm)], ['44', '45'])).
% 0.84/1.02  thf(t5_subset, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.84/1.02          ( v1_xboole_0 @ C ) ) ))).
% 0.84/1.02  thf('47', plain,
% 0.84/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X22 @ X23)
% 0.84/1.02          | ~ (v1_xboole_0 @ X24)
% 0.84/1.02          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t5_subset])).
% 0.84/1.02  thf('48', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['46', '47'])).
% 0.84/1.02  thf('49', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['43', '48'])).
% 0.84/1.02  thf(t28_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.02  thf('50', plain,
% 0.84/1.02      (![X9 : $i, X10 : $i]:
% 0.84/1.02         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.84/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.02  thf('51', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]:
% 0.84/1.02         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['49', '50'])).
% 0.84/1.02  thf('52', plain,
% 0.84/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf(commutativity_k9_subset_1, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.02       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.84/1.02  thf('53', plain,
% 0.84/1.02      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.02         (((k9_subset_1 @ X11 @ X13 @ X12) = (k9_subset_1 @ X11 @ X12 @ X13))
% 0.84/1.02          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.84/1.02      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.84/1.02  thf('54', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.84/1.02           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['52', '53'])).
% 0.84/1.02  thf('55', plain,
% 0.84/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf(redefinition_k9_subset_1, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.02       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.84/1.02  thf('56', plain,
% 0.84/1.02      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.02         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 0.84/1.02          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.84/1.02      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.84/1.02  thf('57', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.84/1.02           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['55', '56'])).
% 0.84/1.02  thf('58', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((k3_xboole_0 @ X0 @ sk_B)
% 0.84/1.02           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.84/1.02      inference('demod', [status(thm)], ['54', '57'])).
% 0.84/1.02  thf(t41_tex_2, axiom,
% 0.84/1.02    (![A:$i]:
% 0.84/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.02       ( ![B:$i]:
% 0.84/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.02           ( ( v2_tex_2 @ B @ A ) <=>
% 0.84/1.02             ( ![C:$i]:
% 0.84/1.02               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.02                 ( ( r1_tarski @ C @ B ) =>
% 0.84/1.02                   ( ( k9_subset_1 @
% 0.84/1.02                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.84/1.02                     ( C ) ) ) ) ) ) ) ) ))).
% 0.84/1.02  thf('59', plain,
% 0.84/1.02      (![X35 : $i, X36 : $i]:
% 0.84/1.02         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.84/1.02          | ((k9_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.84/1.02              (k2_pre_topc @ X36 @ (sk_C_2 @ X35 @ X36)))
% 0.84/1.02              != (sk_C_2 @ X35 @ X36))
% 0.84/1.02          | (v2_tex_2 @ X35 @ X36)
% 0.84/1.02          | ~ (l1_pre_topc @ X36)
% 0.84/1.02          | ~ (v2_pre_topc @ X36)
% 0.84/1.02          | (v2_struct_0 @ X36))),
% 0.84/1.02      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.84/1.02  thf('60', plain,
% 0.84/1.02      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (sk_C_2 @ sk_B @ sk_A)) @ sk_B)
% 0.84/1.02          != (sk_C_2 @ sk_B @ sk_A))
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (v2_tex_2 @ sk_B @ sk_A)
% 0.84/1.02        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['58', '59'])).
% 0.84/1.02  thf(commutativity_k3_xboole_0, axiom,
% 0.84/1.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.84/1.02  thf('61', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.02  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('64', plain,
% 0.84/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('65', plain,
% 0.84/1.02      ((((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ (sk_C_2 @ sk_B @ sk_A)))
% 0.84/1.02          != (sk_C_2 @ sk_B @ sk_A))
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.84/1.02      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.84/1.02  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('67', plain,
% 0.84/1.02      (((v2_tex_2 @ sk_B @ sk_A)
% 0.84/1.02        | ((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ (sk_C_2 @ sk_B @ sk_A)))
% 0.84/1.02            != (sk_C_2 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['65', '66'])).
% 0.84/1.02  thf('68', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('69', plain,
% 0.84/1.02      (((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ (sk_C_2 @ sk_B @ sk_A)))
% 0.84/1.02         != (sk_C_2 @ sk_B @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['67', '68'])).
% 0.84/1.02  thf('70', plain,
% 0.84/1.02      ((((sk_B) != (sk_C_2 @ sk_B @ sk_A)) | ~ (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['51', '69'])).
% 0.84/1.02  thf('71', plain,
% 0.84/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('72', plain,
% 0.84/1.02      (![X35 : $i, X36 : $i]:
% 0.84/1.02         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.84/1.02          | (r1_tarski @ (sk_C_2 @ X35 @ X36) @ X35)
% 0.84/1.02          | (v2_tex_2 @ X35 @ X36)
% 0.84/1.02          | ~ (l1_pre_topc @ X36)
% 0.84/1.02          | ~ (v2_pre_topc @ X36)
% 0.84/1.02          | (v2_struct_0 @ X36))),
% 0.84/1.02      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.84/1.02  thf('73', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (v2_tex_2 @ sk_B @ sk_A)
% 0.84/1.02        | (r1_tarski @ (sk_C_2 @ sk_B @ sk_A) @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['71', '72'])).
% 0.84/1.02  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('76', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | (v2_tex_2 @ sk_B @ sk_A)
% 0.84/1.02        | (r1_tarski @ (sk_C_2 @ sk_B @ sk_A) @ sk_B))),
% 0.84/1.02      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.84/1.02  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('78', plain,
% 0.84/1.02      (((r1_tarski @ (sk_C_2 @ sk_B @ sk_A) @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['76', '77'])).
% 0.84/1.02  thf('79', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('80', plain, ((r1_tarski @ (sk_C_2 @ sk_B @ sk_A) @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['78', '79'])).
% 0.84/1.02  thf('81', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['43', '48'])).
% 0.84/1.02  thf('82', plain,
% 0.84/1.02      (![X6 : $i, X8 : $i]:
% 0.84/1.02         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.84/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.02  thf('83', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]:
% 0.84/1.02         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['81', '82'])).
% 0.84/1.02  thf('84', plain,
% 0.84/1.02      ((((sk_C_2 @ sk_B @ sk_A) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['80', '83'])).
% 0.84/1.02  thf('85', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['70', '84'])).
% 0.84/1.02  thf('86', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (k1_zfmisc_1 @ X0))
% 0.84/1.02          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['42', '85'])).
% 0.84/1.02  thf('87', plain,
% 0.84/1.02      (![X19 : $i, X20 : $i]:
% 0.84/1.02         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.02  thf('88', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.84/1.02          | (r1_tarski @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['86', '87'])).
% 0.84/1.02  thf('89', plain,
% 0.84/1.02      (![X6 : $i, X8 : $i]:
% 0.84/1.02         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.84/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.02  thf('90', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.84/1.02          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02          | ((X0) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['88', '89'])).
% 0.84/1.02  thf('91', plain,
% 0.84/1.02      (![X0 : $i]:
% 0.84/1.02         (~ (r1_tarski @ X0 @ sk_B)
% 0.84/1.02          | (v1_xboole_0 @ sk_B)
% 0.84/1.02          | ((X0) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['30', '90'])).
% 0.84/1.02  thf('92', plain,
% 0.84/1.02      (((r2_hidden @ (sk_C @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['23', '91'])).
% 0.84/1.02  thf('93', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('clc', [status(thm)], ['28', '29'])).
% 0.84/1.02  thf('94', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('clc', [status(thm)], ['92', '93'])).
% 0.84/1.02  thf('95', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['70', '84'])).
% 0.84/1.02  thf('96', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('97', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('98', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('demod', [status(thm)], ['21', '96', '97'])).
% 0.84/1.02  thf('99', plain,
% 0.84/1.02      (((m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('simplify', [status(thm)], ['98'])).
% 0.84/1.02  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('101', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['99', '100'])).
% 0.84/1.02  thf('102', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['70', '84'])).
% 0.84/1.02  thf('103', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.84/1.02      inference('clc', [status(thm)], ['101', '102'])).
% 0.84/1.02  thf('104', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (m1_pre_topc @ 
% 0.84/1.02           (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A) @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['19', '20'])).
% 0.84/1.02  thf(cc5_tdlat_3, axiom,
% 0.84/1.02    (![A:$i]:
% 0.84/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.84/1.02         ( l1_pre_topc @ A ) ) =>
% 0.84/1.02       ( ![B:$i]:
% 0.84/1.02         ( ( m1_pre_topc @ B @ A ) =>
% 0.84/1.02           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 0.84/1.02             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.84/1.02  thf('105', plain,
% 0.84/1.02      (![X28 : $i, X29 : $i]:
% 0.84/1.02         (~ (m1_pre_topc @ X28 @ X29)
% 0.84/1.02          | (v1_tdlat_3 @ X28)
% 0.84/1.02          | ~ (l1_pre_topc @ X29)
% 0.84/1.02          | ~ (v1_tdlat_3 @ X29)
% 0.84/1.02          | ~ (v2_pre_topc @ X29)
% 0.84/1.02          | (v2_struct_0 @ X29))),
% 0.84/1.02      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 0.84/1.02  thf('106', plain,
% 0.84/1.02      (((v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.02        | ~ (v1_tdlat_3 @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | (v1_tdlat_3 @ 
% 0.84/1.02           (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['104', '105'])).
% 0.84/1.02  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('108', plain, ((v1_tdlat_3 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('110', plain,
% 0.84/1.02      (((v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_tdlat_3 @ 
% 0.84/1.02           (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)))),
% 0.84/1.02      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.84/1.02  thf('111', plain,
% 0.84/1.02      (((v1_tdlat_3 @ (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A))
% 0.84/1.02        | (v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('simplify', [status(thm)], ['110'])).
% 0.84/1.02  thf('112', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('113', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('114', plain,
% 0.84/1.02      (((v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | (v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.84/1.02  thf('115', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('simplify', [status(thm)], ['114'])).
% 0.84/1.02  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('117', plain,
% 0.84/1.02      (((v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('clc', [status(thm)], ['115', '116'])).
% 0.84/1.02  thf('118', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['70', '84'])).
% 0.84/1.02  thf('119', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['117', '118'])).
% 0.84/1.02  thf('120', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('121', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | (v2_tex_2 @ sk_B @ sk_A)
% 0.84/1.02        | (v2_struct_0 @ sk_A))),
% 0.84/1.02      inference('demod', [status(thm)], ['16', '103', '119', '120'])).
% 0.84/1.02  thf('122', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.84/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.02  thf('123', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((v1_xboole_0 @ X30)
% 0.84/1.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.84/1.02          | ~ (v2_struct_0 @ (sk_C_1 @ X30 @ X31))
% 0.84/1.02          | ~ (l1_pre_topc @ X31)
% 0.84/1.02          | (v2_struct_0 @ X31))),
% 0.84/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.84/1.02  thf('124', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.02        | ~ (v2_struct_0 @ 
% 0.84/1.02             (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A))
% 0.84/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['122', '123'])).
% 0.84/1.02  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('126', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (v2_struct_0 @ 
% 0.84/1.02             (sk_C_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A))
% 0.84/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.84/1.02      inference('demod', [status(thm)], ['124', '125'])).
% 0.84/1.02  thf('127', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('128', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '95'])).
% 0.84/1.02  thf('129', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B)
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.84/1.02  thf('130', plain,
% 0.84/1.02      ((~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.84/1.02        | (v2_struct_0 @ sk_A)
% 0.84/1.02        | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('simplify', [status(thm)], ['129'])).
% 0.84/1.02  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('132', plain,
% 0.84/1.02      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.84/1.02      inference('clc', [status(thm)], ['130', '131'])).
% 0.84/1.02  thf('133', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['70', '84'])).
% 0.84/1.02  thf('134', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['132', '133'])).
% 0.84/1.02  thf('135', plain,
% 0.84/1.02      (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.84/1.02      inference('sup-', [status(thm)], ['121', '134'])).
% 0.84/1.02  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('137', plain, (((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.84/1.02      inference('clc', [status(thm)], ['135', '136'])).
% 0.84/1.02  thf('138', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.84/1.02      inference('clc', [status(thm)], ['70', '84'])).
% 0.84/1.02  thf('139', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.84/1.02      inference('clc', [status(thm)], ['137', '138'])).
% 0.84/1.02  thf('140', plain, ($false), inference('demod', [status(thm)], ['0', '139'])).
% 0.84/1.02  
% 0.84/1.02  % SZS output end Refutation
% 0.84/1.02  
% 0.84/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
