%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aj3wQ0qYJZ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:39 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 338 expanded)
%              Number of leaves         :   40 ( 111 expanded)
%              Depth                    :   33
%              Number of atoms          : 1695 (3841 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(t36_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X30
        = ( u1_struct_0 @ ( sk_C_1 @ X30 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X30 @ X31 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( l1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( l1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('29',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('30',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_1 @ X28 ) @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(d1_tex_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( ( v7_struct_0 @ A )
      <=> ? [B: $i] :
            ( ( ( u1_struct_0 @ A )
              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( u1_struct_0 @ X26 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( v7_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ ( k1_tarski @ X0 ) @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k6_domain_1 @ ( k1_tarski @ X0 ) @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28
       != ( k6_domain_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( v1_zfmisc_1 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['27','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) )
    | ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','53'])).

thf('55',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X30 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( l1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('64',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(cc25_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B )
              & ( v2_pre_topc @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( v2_tdlat_3 @ B ) ) ) ) ) )).

thf('65',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( v7_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc25_tex_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ~ ( v7_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,
    ( ~ ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','73'])).

thf('75',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('78',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

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

thf('82',plain,(
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

thf('83',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X32 ) @ X33 )
      | ~ ( v1_tdlat_3 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','87'])).

thf('89',plain,
    ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','89'])).

thf('91',plain,
    ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('95',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('99',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v2_tex_2 @ ( k1_tarski @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('107',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('108',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aj3wQ0qYJZ
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 312 iterations in 0.228s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.64  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.64  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.64  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.46/0.64  thf(t36_tex_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.64            ( l1_pre_topc @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.46/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t2_subset, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         ((r2_hidden @ X11 @ X12)
% 0.46/0.64          | (v1_xboole_0 @ X12)
% 0.46/0.64          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(t63_subset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.64       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.46/0.64          | ~ (r2_hidden @ X7 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(t10_tsep_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.64             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.64           ( ?[C:$i]:
% 0.46/0.64             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.46/0.64               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X30 : $i, X31 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X30)
% 0.46/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.64          | ((X30) = (u1_struct_0 @ (sk_C_1 @ X30 @ X31)))
% 0.46/0.64          | ~ (l1_pre_topc @ X31)
% 0.46/0.64          | (v2_struct_0 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | ((k1_tarski @ sk_B_2)
% 0.46/0.64            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.64        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | ((k1_tarski @ sk_B_2)
% 0.46/0.64            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.64        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.64      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X30 : $i, X31 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X30)
% 0.46/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.64          | (m1_pre_topc @ (sk_C_1 @ X30 @ X31) @ X31)
% 0.46/0.64          | ~ (l1_pre_topc @ X31)
% 0.46/0.64          | (v2_struct_0 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(cc1_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (m1_pre_topc @ X13 @ X14)
% 0.46/0.64          | (v2_pre_topc @ X13)
% 0.46/0.64          | ~ (l1_pre_topc @ X14)
% 0.46/0.64          | ~ (v2_pre_topc @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ((k1_tarski @ sk_B_2)
% 0.46/0.65            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf(dt_m1_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (m1_pre_topc @ X16 @ X17)
% 0.46/0.65          | (l1_pre_topc @ X16)
% 0.46/0.65          | ~ (l1_pre_topc @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (l1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (l1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(dt_l1_pre_topc, axiom,
% 0.46/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (l1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ((k1_tarski @ sk_B_2)
% 0.46/0.65            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf(d1_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65       ( ( v1_zfmisc_1 @ A ) <=>
% 0.46/0.65         ( ?[B:$i]:
% 0.46/0.65           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X28 : $i]:
% 0.46/0.65         (~ (v1_zfmisc_1 @ X28)
% 0.46/0.65          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_1 @ X28)))
% 0.46/0.65          | (v1_xboole_0 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X28 : $i]:
% 0.46/0.65         (~ (v1_zfmisc_1 @ X28)
% 0.46/0.65          | (m1_subset_1 @ (sk_B_1 @ X28) @ X28)
% 0.46/0.65          | (v1_xboole_0 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.46/0.65  thf(d1_tex_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ( v7_struct_0 @ A ) <=>
% 0.46/0.65         ( ?[B:$i]:
% 0.46/0.65           ( ( ( u1_struct_0 @ A ) = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) & 
% 0.46/0.65             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i]:
% 0.46/0.65         (((u1_struct_0 @ X26) != (k6_domain_1 @ (u1_struct_0 @ X26) @ X27))
% 0.46/0.65          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.46/0.65          | (v7_struct_0 @ X26)
% 0.46/0.65          | ~ (l1_struct_0 @ X26)
% 0.46/0.65          | (v2_struct_0 @ X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tex_1])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v7_struct_0 @ X0)
% 0.46/0.65          | ((u1_struct_0 @ X0)
% 0.46/0.65              != (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.65                  (sk_B_1 @ (u1_struct_0 @ X0)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((u1_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v7_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['29', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v7_struct_0 @ X0)
% 0.46/0.65          | ~ (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.65        | (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '34'])).
% 0.46/0.65  thf(d1_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.65  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.46/0.65  thf(t1_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.65  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_tarski @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X19)
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ X19)
% 0.46/0.65          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k6_domain_1 @ (k1_tarski @ X0) @ X0) = (k1_tarski @ X0))
% 0.46/0.65          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.46/0.65  thf('42', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X0 : $i]: ((k6_domain_1 @ (k1_tarski @ X0) @ X0) = (k1_tarski @ X0))),
% 0.46/0.65      inference('clc', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i]:
% 0.46/0.65         (((X28) != (k6_domain_1 @ X28 @ X29))
% 0.46/0.65          | ~ (m1_subset_1 @ X29 @ X28)
% 0.46/0.65          | (v1_zfmisc_1 @ X28)
% 0.46/0.65          | (v1_xboole_0 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.46/0.65          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.46/0.65          | (v1_zfmisc_1 @ (k1_tarski @ X0))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_tarski @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.46/0.65          | (v1_xboole_0 @ (k1_tarski @ X0))
% 0.46/0.65          | (v1_zfmisc_1 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_zfmisc_1 @ (k1_tarski @ X0)) | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.65  thf('49', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.46/0.65  thf('50', plain, (![X0 : $i]: (v1_zfmisc_1 @ (k1_tarski @ X0))),
% 0.46/0.65      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.65        | (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['35', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))
% 0.46/0.65        | (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['20', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (((v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X30 : $i, X31 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X30)
% 0.46/0.65          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.65          | ~ (v2_struct_0 @ (sk_C_1 @ X30 @ X31))
% 0.46/0.65          | ~ (l1_pre_topc @ X31)
% 0.46/0.65          | (v2_struct_0 @ X31))),
% 0.46/0.65      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['55', '60'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (((v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (l1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(t2_tsep_1, axiom,
% 0.46/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.46/0.65  thf(cc25_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.65           ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.46/0.65               ( v2_pre_topc @ B ) ) =>
% 0.46/0.65             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.46/0.65               ( v2_tdlat_3 @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i]:
% 0.46/0.65         (~ (m1_pre_topc @ X24 @ X25)
% 0.46/0.65          | (v1_tdlat_3 @ X24)
% 0.46/0.65          | ~ (v2_pre_topc @ X24)
% 0.46/0.65          | ~ (v7_struct_0 @ X24)
% 0.46/0.65          | (v2_struct_0 @ X24)
% 0.46/0.65          | ~ (l1_pre_topc @ X25)
% 0.46/0.65          | (v2_struct_0 @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc25_tex_2])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v7_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | (v1_tdlat_3 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_tdlat_3 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (v7_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      ((~ (l1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['63', '69'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      ((~ (v7_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '71'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      ((~ (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (((v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['74'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf(t1_tsep_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.65           ( m1_subset_1 @
% 0.46/0.65             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i]:
% 0.46/0.65         (~ (m1_pre_topc @ X21 @ X22)
% 0.46/0.65          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.65          | ~ (l1_pre_topc @ X22))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (m1_subset_1 @ 
% 0.46/0.65           (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ 
% 0.46/0.65           (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf(t26_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.46/0.65                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X32)
% 0.46/0.65          | ~ (m1_pre_topc @ X32 @ X33)
% 0.46/0.65          | ((X34) != (u1_struct_0 @ X32))
% 0.46/0.65          | ~ (v1_tdlat_3 @ X32)
% 0.46/0.65          | (v2_tex_2 @ X34 @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.46/0.65          | ~ (l1_pre_topc @ X33)
% 0.46/0.65          | (v2_struct_0 @ X33))),
% 0.46/0.65      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (![X32 : $i, X33 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X33)
% 0.46/0.65          | ~ (l1_pre_topc @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.46/0.65          | (v2_tex_2 @ (u1_struct_0 @ X32) @ X33)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X32)
% 0.46/0.65          | ~ (m1_pre_topc @ X32 @ X33)
% 0.46/0.65          | (v2_struct_0 @ X32))),
% 0.46/0.65      inference('simplify', [status(thm)], ['82'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.65        | ~ (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65           sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['81', '83'])).
% 0.46/0.65  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.65        | ~ (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65           sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      (((v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65         sk_A)
% 0.46/0.65        | ~ (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A) @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | ~ (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65           sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['76', '87'])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      (((v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65         sk_A)
% 0.46/0.65        | ~ (v1_tdlat_3 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65           sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['75', '89'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (((v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)) @ 
% 0.46/0.65         sk_A)
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['90'])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      (((v2_tex_2 @ (k1_tarski @ sk_B_2) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['9', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_tex_2 @ (k1_tarski @ sk_B_2) @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['92'])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B_2) @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (((v2_tex_2 @ (k1_tarski @ sk_B_2) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_tex_2 @ (k1_tarski @ sk_B_2) @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.65  thf('97', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('98', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X19)
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ X19)
% 0.46/0.65          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      ((~ (v2_tex_2 @ (k1_tarski @ sk_B_2) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.65  thf('102', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['96', '101'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.65  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('105', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['103', '104'])).
% 0.46/0.65  thf('106', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.46/0.65  thf('107', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['105', '106'])).
% 0.46/0.65  thf(fc2_struct_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('108', plain,
% 0.46/0.65      (![X18 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.46/0.65          | ~ (l1_struct_0 @ X18)
% 0.46/0.65          | (v2_struct_0 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.65  thf('109', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.65  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.65  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.65  thf('113', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['109', '112'])).
% 0.46/0.65  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.49/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
