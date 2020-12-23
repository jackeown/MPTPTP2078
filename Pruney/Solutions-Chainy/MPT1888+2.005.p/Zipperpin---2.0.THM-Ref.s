%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E3GBz44ssv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:28 EST 2020

% Result     : Theorem 13.18s
% Output     : Refutation 13.18s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 188 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   23
%              Number of atoms          : 1108 (3417 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t56_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                  | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                    = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_tdlat_3 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t40_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_xboole_0 @ B @ C )
                  & ( v3_pre_topc @ B @ A ) )
               => ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ X28 )
      | ( r1_xboole_0 @ X26 @ ( k2_pre_topc @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('48',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('51',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['45','55'])).

thf('57',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t55_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
               => ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X29 @ ( k2_pre_topc @ X30 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X31 ) ) )
      | ( ( k2_pre_topc @ X30 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) )
        = ( k2_pre_topc @ X30 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v3_tdlat_3 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('76',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E3GBz44ssv
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:55:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 13.18/13.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.18/13.38  % Solved by: fo/fo7.sh
% 13.18/13.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.18/13.38  % done 7166 iterations in 12.934s
% 13.18/13.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.18/13.38  % SZS output start Refutation
% 13.18/13.38  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 13.18/13.38  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 13.18/13.38  thf(sk_C_2_type, type, sk_C_2: $i).
% 13.18/13.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.18/13.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.18/13.38  thf(sk_A_type, type, sk_A: $i).
% 13.18/13.38  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 13.18/13.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.18/13.38  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 13.18/13.38  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 13.18/13.38  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 13.18/13.38  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 13.18/13.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.18/13.38  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 13.18/13.38  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 13.18/13.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.18/13.38  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 13.18/13.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.18/13.38  thf(sk_B_2_type, type, sk_B_2: $i).
% 13.18/13.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.18/13.38  thf(t56_tex_2, conjecture,
% 13.18/13.38    (![A:$i]:
% 13.18/13.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 13.18/13.38         ( l1_pre_topc @ A ) ) =>
% 13.18/13.38       ( ![B:$i]:
% 13.18/13.38         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 13.18/13.38           ( ![C:$i]:
% 13.18/13.38             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 13.18/13.38               ( ( r1_xboole_0 @
% 13.18/13.38                   ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 13.18/13.38                   ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 13.18/13.38                 ( ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 13.18/13.38                   ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 13.18/13.38  thf(zf_stmt_0, negated_conjecture,
% 13.18/13.38    (~( ![A:$i]:
% 13.18/13.38        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 13.18/13.38            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.18/13.38          ( ![B:$i]:
% 13.18/13.38            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 13.18/13.38              ( ![C:$i]:
% 13.18/13.38                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 13.18/13.38                  ( ( r1_xboole_0 @
% 13.18/13.38                      ( k2_pre_topc @
% 13.18/13.38                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 13.18/13.38                      ( k2_pre_topc @
% 13.18/13.38                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 13.18/13.38                    ( ( k2_pre_topc @
% 13.18/13.38                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 13.18/13.38                      ( k2_pre_topc @
% 13.18/13.38                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 13.18/13.38    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 13.18/13.38  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf(t2_subset, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( m1_subset_1 @ A @ B ) =>
% 13.18/13.38       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 13.18/13.38  thf('2', plain,
% 13.18/13.38      (![X14 : $i, X15 : $i]:
% 13.18/13.38         ((r2_hidden @ X14 @ X15)
% 13.18/13.38          | (v1_xboole_0 @ X15)
% 13.18/13.38          | ~ (m1_subset_1 @ X14 @ X15))),
% 13.18/13.38      inference('cnf', [status(esa)], [t2_subset])).
% 13.18/13.38  thf('3', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['1', '2'])).
% 13.18/13.38  thf(t63_subset_1, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( r2_hidden @ A @ B ) =>
% 13.18/13.38       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 13.18/13.38  thf('4', plain,
% 13.18/13.38      (![X12 : $i, X13 : $i]:
% 13.18/13.38         ((m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X13))
% 13.18/13.38          | ~ (r2_hidden @ X12 @ X13))),
% 13.18/13.38      inference('cnf', [status(esa)], [t63_subset_1])).
% 13.18/13.38  thf('5', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 13.18/13.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.18/13.38      inference('sup-', [status(thm)], ['3', '4'])).
% 13.18/13.38  thf(t3_xboole_0, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 13.18/13.38            ( r1_xboole_0 @ A @ B ) ) ) & 
% 13.18/13.38       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 13.18/13.38            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 13.18/13.38  thf('6', plain,
% 13.18/13.38      (![X3 : $i, X4 : $i]:
% 13.18/13.38         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 13.18/13.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 13.18/13.38  thf(d1_tarski, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 13.18/13.38       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 13.18/13.38  thf('7', plain,
% 13.18/13.38      (![X7 : $i, X9 : $i, X10 : $i]:
% 13.18/13.38         (~ (r2_hidden @ X10 @ X9)
% 13.18/13.38          | ((X10) = (X7))
% 13.18/13.38          | ((X9) != (k1_tarski @ X7)))),
% 13.18/13.38      inference('cnf', [status(esa)], [d1_tarski])).
% 13.18/13.38  thf('8', plain,
% 13.18/13.38      (![X7 : $i, X10 : $i]:
% 13.18/13.38         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 13.18/13.38      inference('simplify', [status(thm)], ['7'])).
% 13.18/13.38  thf('9', plain,
% 13.18/13.38      (![X0 : $i, X1 : $i]:
% 13.18/13.38         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 13.18/13.38          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['6', '8'])).
% 13.18/13.38  thf('10', plain,
% 13.18/13.38      (![X3 : $i, X4 : $i]:
% 13.18/13.38         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 13.18/13.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 13.18/13.38  thf('11', plain,
% 13.18/13.38      (![X0 : $i, X1 : $i]:
% 13.18/13.38         ((r2_hidden @ X0 @ X1)
% 13.18/13.38          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 13.18/13.38          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 13.18/13.38      inference('sup+', [status(thm)], ['9', '10'])).
% 13.18/13.38  thf('12', plain,
% 13.18/13.38      (![X0 : $i, X1 : $i]:
% 13.18/13.38         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 13.18/13.38      inference('simplify', [status(thm)], ['11'])).
% 13.18/13.38  thf('13', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('14', plain,
% 13.18/13.38      (![X14 : $i, X15 : $i]:
% 13.18/13.38         ((r2_hidden @ X14 @ X15)
% 13.18/13.38          | (v1_xboole_0 @ X15)
% 13.18/13.38          | ~ (m1_subset_1 @ X14 @ X15))),
% 13.18/13.38      inference('cnf', [status(esa)], [t2_subset])).
% 13.18/13.38  thf('15', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['13', '14'])).
% 13.18/13.38  thf('16', plain,
% 13.18/13.38      (![X12 : $i, X13 : $i]:
% 13.18/13.38         ((m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X13))
% 13.18/13.38          | ~ (r2_hidden @ X12 @ X13))),
% 13.18/13.38      inference('cnf', [status(esa)], [t63_subset_1])).
% 13.18/13.38  thf('17', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 13.18/13.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.18/13.38      inference('sup-', [status(thm)], ['15', '16'])).
% 13.18/13.38  thf(dt_k2_pre_topc, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( ( l1_pre_topc @ A ) & 
% 13.18/13.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 13.18/13.38       ( m1_subset_1 @
% 13.18/13.38         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 13.18/13.38  thf('18', plain,
% 13.18/13.38      (![X16 : $i, X17 : $i]:
% 13.18/13.38         (~ (l1_pre_topc @ X16)
% 13.18/13.38          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 13.18/13.38          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 13.18/13.38             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 13.18/13.38      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 13.18/13.38  thf('19', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.18/13.38        | ~ (l1_pre_topc @ sk_A))),
% 13.18/13.38      inference('sup-', [status(thm)], ['17', '18'])).
% 13.18/13.38  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('21', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.18/13.38      inference('demod', [status(thm)], ['19', '20'])).
% 13.18/13.38  thf(t24_tdlat_3, axiom,
% 13.18/13.38    (![A:$i]:
% 13.18/13.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.18/13.38       ( ( v3_tdlat_3 @ A ) <=>
% 13.18/13.38         ( ![B:$i]:
% 13.18/13.38           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.18/13.38             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 13.18/13.38  thf('22', plain,
% 13.18/13.38      (![X24 : $i, X25 : $i]:
% 13.18/13.38         (~ (v3_tdlat_3 @ X24)
% 13.18/13.38          | ~ (v4_pre_topc @ X25 @ X24)
% 13.18/13.38          | (v3_pre_topc @ X25 @ X24)
% 13.18/13.38          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 13.18/13.38          | ~ (l1_pre_topc @ X24)
% 13.18/13.38          | ~ (v2_pre_topc @ X24))),
% 13.18/13.38      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 13.18/13.38  thf('23', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | ~ (v2_pre_topc @ sk_A)
% 13.18/13.38        | ~ (l1_pre_topc @ sk_A)
% 13.18/13.38        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 13.18/13.38        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 13.18/13.38        | ~ (v3_tdlat_3 @ sk_A))),
% 13.18/13.38      inference('sup-', [status(thm)], ['21', '22'])).
% 13.18/13.38  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('26', plain, ((v3_tdlat_3 @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('27', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 13.18/13.38        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 13.18/13.38      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 13.18/13.38  thf('28', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 13.18/13.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.18/13.38      inference('sup-', [status(thm)], ['15', '16'])).
% 13.18/13.38  thf(fc1_tops_1, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 13.18/13.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 13.18/13.38       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 13.18/13.38  thf('29', plain,
% 13.18/13.38      (![X22 : $i, X23 : $i]:
% 13.18/13.38         (~ (l1_pre_topc @ X22)
% 13.18/13.38          | ~ (v2_pre_topc @ X22)
% 13.18/13.38          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 13.18/13.38          | (v4_pre_topc @ (k2_pre_topc @ X22 @ X23) @ X22))),
% 13.18/13.38      inference('cnf', [status(esa)], [fc1_tops_1])).
% 13.18/13.38  thf('30', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 13.18/13.38        | ~ (v2_pre_topc @ sk_A)
% 13.18/13.38        | ~ (l1_pre_topc @ sk_A))),
% 13.18/13.38      inference('sup-', [status(thm)], ['28', '29'])).
% 13.18/13.38  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('33', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 13.18/13.38      inference('demod', [status(thm)], ['30', '31', '32'])).
% 13.18/13.38  thf('34', plain,
% 13.18/13.38      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('clc', [status(thm)], ['27', '33'])).
% 13.18/13.38  thf('35', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.18/13.38      inference('demod', [status(thm)], ['19', '20'])).
% 13.18/13.38  thf(t40_tsep_1, axiom,
% 13.18/13.38    (![A:$i]:
% 13.18/13.38     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.18/13.38       ( ![B:$i]:
% 13.18/13.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.18/13.38           ( ![C:$i]:
% 13.18/13.38             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.18/13.38               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 13.18/13.38                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 13.18/13.38  thf('36', plain,
% 13.18/13.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.18/13.38         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 13.18/13.38          | ~ (v3_pre_topc @ X26 @ X27)
% 13.18/13.38          | ~ (r1_xboole_0 @ X26 @ X28)
% 13.18/13.38          | (r1_xboole_0 @ X26 @ (k2_pre_topc @ X27 @ X28))
% 13.18/13.38          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 13.18/13.38          | ~ (l1_pre_topc @ X27)
% 13.18/13.38          | ~ (v2_pre_topc @ X27))),
% 13.18/13.38      inference('cnf', [status(esa)], [t40_tsep_1])).
% 13.18/13.38  thf('37', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | ~ (v2_pre_topc @ sk_A)
% 13.18/13.38          | ~ (l1_pre_topc @ sk_A)
% 13.18/13.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.18/13.38          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38             (k2_pre_topc @ sk_A @ X0))
% 13.18/13.38          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 13.18/13.38          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 13.18/13.38      inference('sup-', [status(thm)], ['35', '36'])).
% 13.18/13.38  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('40', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.18/13.38          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38             (k2_pre_topc @ sk_A @ X0))
% 13.18/13.38          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 13.18/13.38          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 13.18/13.38      inference('demod', [status(thm)], ['37', '38', '39'])).
% 13.18/13.38  thf('41', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 13.18/13.38          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38             (k2_pre_topc @ sk_A @ X0))
% 13.18/13.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.18/13.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['34', '40'])).
% 13.18/13.38  thf('42', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.18/13.38          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38             (k2_pre_topc @ sk_A @ X0))
% 13.18/13.38          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 13.18/13.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('simplify', [status(thm)], ['41'])).
% 13.18/13.38  thf('43', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 13.18/13.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 13.18/13.38          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 13.18/13.38               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 13.18/13.38      inference('sup-', [status(thm)], ['12', '42'])).
% 13.18/13.38  thf('44', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (r2_hidden @ sk_C_2 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 13.18/13.38      inference('sup-', [status(thm)], ['5', '43'])).
% 13.18/13.38  thf('45', plain,
% 13.18/13.38      (((r2_hidden @ sk_C_2 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 13.18/13.38        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('simplify', [status(thm)], ['44'])).
% 13.18/13.38  thf('46', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf(redefinition_k6_domain_1, axiom,
% 13.18/13.38    (![A:$i,B:$i]:
% 13.18/13.38     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 13.18/13.38       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 13.18/13.38  thf('47', plain,
% 13.18/13.38      (![X20 : $i, X21 : $i]:
% 13.18/13.38         ((v1_xboole_0 @ X20)
% 13.18/13.38          | ~ (m1_subset_1 @ X21 @ X20)
% 13.18/13.38          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 13.18/13.38      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 13.18/13.38  thf('48', plain,
% 13.18/13.38      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['46', '47'])).
% 13.18/13.38  thf('49', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('50', plain,
% 13.18/13.38      (![X20 : $i, X21 : $i]:
% 13.18/13.38         ((v1_xboole_0 @ X20)
% 13.18/13.38          | ~ (m1_subset_1 @ X21 @ X20)
% 13.18/13.38          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 13.18/13.38      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 13.18/13.38  thf('51', plain,
% 13.18/13.38      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['49', '50'])).
% 13.18/13.38  thf('52', plain,
% 13.18/13.38      (~ (r1_xboole_0 @ 
% 13.18/13.38          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 13.18/13.38          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('53', plain,
% 13.18/13.38      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['51', '52'])).
% 13.18/13.38  thf('54', plain,
% 13.18/13.38      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['48', '53'])).
% 13.18/13.38  thf('55', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 13.18/13.38             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))))),
% 13.18/13.38      inference('simplify', [status(thm)], ['54'])).
% 13.18/13.38  thf('56', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | (r2_hidden @ sk_C_2 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 13.18/13.38      inference('clc', [status(thm)], ['45', '55'])).
% 13.18/13.38  thf('57', plain,
% 13.18/13.38      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['49', '50'])).
% 13.18/13.38  thf(t55_tex_2, axiom,
% 13.18/13.38    (![A:$i]:
% 13.18/13.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 13.18/13.38         ( l1_pre_topc @ A ) ) =>
% 13.18/13.38       ( ![B:$i]:
% 13.18/13.38         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 13.18/13.38           ( ![C:$i]:
% 13.18/13.38             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 13.18/13.38               ( ( r2_hidden @
% 13.18/13.38                   B @ 
% 13.18/13.38                   ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 13.18/13.38                 ( ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 13.18/13.38                   ( k2_pre_topc @
% 13.18/13.38                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 13.18/13.38  thf('58', plain,
% 13.18/13.38      (![X29 : $i, X30 : $i, X31 : $i]:
% 13.18/13.38         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 13.18/13.38          | ~ (r2_hidden @ X29 @ 
% 13.18/13.38               (k2_pre_topc @ X30 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X31)))
% 13.18/13.38          | ((k2_pre_topc @ X30 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29))
% 13.18/13.38              = (k2_pre_topc @ X30 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X31)))
% 13.18/13.38          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 13.18/13.38          | ~ (l1_pre_topc @ X30)
% 13.18/13.38          | ~ (v3_tdlat_3 @ X30)
% 13.18/13.38          | ~ (v2_pre_topc @ X30)
% 13.18/13.38          | (v2_struct_0 @ X30))),
% 13.18/13.38      inference('cnf', [status(esa)], [t55_tex_2])).
% 13.18/13.38  thf('59', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 13.18/13.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | (v2_struct_0 @ sk_A)
% 13.18/13.38          | ~ (v2_pre_topc @ sk_A)
% 13.18/13.38          | ~ (v3_tdlat_3 @ sk_A)
% 13.18/13.38          | ~ (l1_pre_topc @ sk_A)
% 13.18/13.38          | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 13.18/13.38              = (k2_pre_topc @ sk_A @ 
% 13.18/13.38                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 13.18/13.38          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['57', '58'])).
% 13.18/13.38  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('61', plain, ((v3_tdlat_3 @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('63', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('64', plain,
% 13.18/13.38      (![X0 : $i]:
% 13.18/13.38         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 13.18/13.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38          | (v2_struct_0 @ sk_A)
% 13.18/13.38          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 13.18/13.38              = (k2_pre_topc @ sk_A @ 
% 13.18/13.38                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 13.18/13.38          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 13.18/13.38  thf('65', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | ~ (m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 13.18/13.38            = (k2_pre_topc @ sk_A @ 
% 13.18/13.38               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 13.18/13.38        | (v2_struct_0 @ sk_A)
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('sup-', [status(thm)], ['56', '64'])).
% 13.18/13.38  thf('66', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('67', plain,
% 13.18/13.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 13.18/13.38        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 13.18/13.38            = (k2_pre_topc @ sk_A @ 
% 13.18/13.38               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 13.18/13.38        | (v2_struct_0 @ sk_A)
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('demod', [status(thm)], ['65', '66'])).
% 13.18/13.38  thf('68', plain,
% 13.18/13.38      (((v2_struct_0 @ sk_A)
% 13.18/13.38        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))
% 13.18/13.38            = (k2_pre_topc @ sk_A @ 
% 13.18/13.38               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 13.18/13.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('simplify', [status(thm)], ['67'])).
% 13.18/13.38  thf('69', plain,
% 13.18/13.38      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 13.18/13.38         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('70', plain,
% 13.18/13.38      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 13.18/13.38      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 13.18/13.38  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf('72', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 13.18/13.38      inference('clc', [status(thm)], ['70', '71'])).
% 13.18/13.38  thf(fc2_struct_0, axiom,
% 13.18/13.38    (![A:$i]:
% 13.18/13.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 13.18/13.38       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 13.18/13.38  thf('73', plain,
% 13.18/13.38      (![X19 : $i]:
% 13.18/13.38         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 13.18/13.38          | ~ (l1_struct_0 @ X19)
% 13.18/13.38          | (v2_struct_0 @ X19))),
% 13.18/13.38      inference('cnf', [status(esa)], [fc2_struct_0])).
% 13.18/13.38  thf('74', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 13.18/13.38      inference('sup-', [status(thm)], ['72', '73'])).
% 13.18/13.38  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 13.18/13.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.18/13.38  thf(dt_l1_pre_topc, axiom,
% 13.18/13.38    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 13.18/13.38  thf('76', plain,
% 13.18/13.38      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 13.18/13.38      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 13.18/13.38  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 13.18/13.38      inference('sup-', [status(thm)], ['75', '76'])).
% 13.18/13.38  thf('78', plain, ((v2_struct_0 @ sk_A)),
% 13.18/13.38      inference('demod', [status(thm)], ['74', '77'])).
% 13.18/13.38  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 13.18/13.38  
% 13.18/13.38  % SZS output end Refutation
% 13.18/13.38  
% 13.18/13.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
