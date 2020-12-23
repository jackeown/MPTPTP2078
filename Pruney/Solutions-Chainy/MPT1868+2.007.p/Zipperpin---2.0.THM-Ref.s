%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xh9S91IpZ5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:40 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 646 expanded)
%              Number of leaves         :   33 ( 194 expanded)
%              Depth                    :   36
%              Number of atoms          : 1639 (8326 expanded)
%              Number of equality atoms :   38 ( 163 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_pre_topc @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X27
        = ( u1_struct_0 @ ( sk_C_1 @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('23',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( ( u1_struct_0 @ X26 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) )
      | ( X26
        = ( k1_tex_2 @ X25 @ X24 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('50',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_pre_topc @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
           => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
              & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v1_tdlat_3 @ ( k1_tex_2 @ X30 @ X29 ) )
      | ~ ( v2_pre_topc @ ( k1_tex_2 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t24_tex_2])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

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

thf('68',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( X33
       != ( u1_struct_0 @ X31 ) )
      | ~ ( v1_tdlat_3 @ X31 )
      | ( v2_tex_2 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X31 ) @ X32 )
      | ~ ( v1_tdlat_3 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('83',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('88',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v2_tex_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('94',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('97',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('105',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xh9S91IpZ5
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.03  % Solved by: fo/fo7.sh
% 0.83/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.03  % done 981 iterations in 0.573s
% 0.83/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.03  % SZS output start Refutation
% 0.83/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.03  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.83/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.03  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.83/1.03  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.83/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.83/1.03  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.83/1.03  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.83/1.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.03  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.83/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.83/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.03  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.83/1.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.03  thf(d1_tarski, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.83/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.83/1.03  thf('0', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.03         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.83/1.03      inference('cnf', [status(esa)], [d1_tarski])).
% 0.83/1.03  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.83/1.03      inference('simplify', [status(thm)], ['0'])).
% 0.83/1.03  thf(t36_tex_2, conjecture,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.83/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.03    (~( ![A:$i]:
% 0.83/1.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.83/1.03            ( l1_pre_topc @ A ) ) =>
% 0.83/1.03          ( ![B:$i]:
% 0.83/1.03            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.83/1.03    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.83/1.03  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(t2_subset, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( m1_subset_1 @ A @ B ) =>
% 0.83/1.03       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.83/1.03  thf('3', plain,
% 0.83/1.03      (![X8 : $i, X9 : $i]:
% 0.83/1.03         ((r2_hidden @ X8 @ X9)
% 0.83/1.03          | (v1_xboole_0 @ X9)
% 0.83/1.03          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.83/1.03      inference('cnf', [status(esa)], [t2_subset])).
% 0.83/1.03  thf('4', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.83/1.03  thf(t63_subset_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( r2_hidden @ A @ B ) =>
% 0.83/1.03       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.83/1.03  thf('5', plain,
% 0.83/1.03      (![X6 : $i, X7 : $i]:
% 0.83/1.03         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.83/1.03          | ~ (r2_hidden @ X6 @ X7))),
% 0.83/1.03      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.83/1.03  thf('6', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf(t10_tsep_1, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.83/1.03             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/1.03           ( ?[C:$i]:
% 0.83/1.03             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.83/1.03               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.83/1.03  thf('7', plain,
% 0.83/1.03      (![X27 : $i, X28 : $i]:
% 0.83/1.03         ((v1_xboole_0 @ X27)
% 0.83/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.83/1.03          | (v1_pre_topc @ (sk_C_1 @ X27 @ X28))
% 0.83/1.03          | ~ (l1_pre_topc @ X28)
% 0.83/1.03          | (v2_struct_0 @ X28))),
% 0.83/1.03      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.83/1.03  thf('8', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.03  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('10', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['8', '9'])).
% 0.83/1.03  thf('11', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('12', plain,
% 0.83/1.03      (![X27 : $i, X28 : $i]:
% 0.83/1.03         ((v1_xboole_0 @ X27)
% 0.83/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.83/1.03          | (m1_pre_topc @ (sk_C_1 @ X27 @ X28) @ X28)
% 0.83/1.03          | ~ (l1_pre_topc @ X28)
% 0.83/1.03          | (v2_struct_0 @ X28))),
% 0.83/1.03      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.83/1.03  thf('13', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.03  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('15', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.83/1.03  thf('16', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('17', plain,
% 0.83/1.03      (![X27 : $i, X28 : $i]:
% 0.83/1.03         ((v1_xboole_0 @ X27)
% 0.83/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.83/1.03          | ((X27) = (u1_struct_0 @ (sk_C_1 @ X27 @ X28)))
% 0.83/1.03          | ~ (l1_pre_topc @ X28)
% 0.83/1.03          | (v2_struct_0 @ X28))),
% 0.83/1.03      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.83/1.03  thf('18', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | ((k1_tarski @ sk_B)
% 0.83/1.03            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.03  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('20', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ((k1_tarski @ sk_B)
% 0.83/1.03            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['18', '19'])).
% 0.83/1.03  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(redefinition_k6_domain_1, axiom,
% 0.83/1.03    (![A:$i,B:$i]:
% 0.83/1.03     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.83/1.03       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.83/1.03  thf('22', plain,
% 0.83/1.03      (![X22 : $i, X23 : $i]:
% 0.83/1.03         ((v1_xboole_0 @ X22)
% 0.83/1.03          | ~ (m1_subset_1 @ X23 @ X22)
% 0.83/1.03          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.83/1.03      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.83/1.03  thf('23', plain,
% 0.83/1.03      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.03  thf(d4_tex_2, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03           ( ![C:$i]:
% 0.83/1.03             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.83/1.03                 ( m1_pre_topc @ C @ A ) ) =>
% 0.83/1.03               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.83/1.03                 ( ( u1_struct_0 @ C ) =
% 0.83/1.03                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.83/1.03  thf('24', plain,
% 0.83/1.03      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.83/1.03          | ((u1_struct_0 @ X26) != (k6_domain_1 @ (u1_struct_0 @ X25) @ X24))
% 0.83/1.03          | ((X26) = (k1_tex_2 @ X25 @ X24))
% 0.83/1.03          | ~ (m1_pre_topc @ X26 @ X25)
% 0.83/1.03          | ~ (v1_pre_topc @ X26)
% 0.83/1.03          | (v2_struct_0 @ X26)
% 0.83/1.03          | ~ (l1_pre_topc @ X25)
% 0.83/1.03          | (v2_struct_0 @ X25))),
% 0.83/1.03      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.83/1.03  thf('25', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (((u1_struct_0 @ X0) != (k1_tarski @ sk_B))
% 0.83/1.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (v2_struct_0 @ sk_A)
% 0.83/1.03          | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03          | (v2_struct_0 @ X0)
% 0.83/1.03          | ~ (v1_pre_topc @ X0)
% 0.83/1.03          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.03          | ((X0) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['23', '24'])).
% 0.83/1.03  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('28', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (((u1_struct_0 @ X0) != (k1_tarski @ sk_B))
% 0.83/1.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (v2_struct_0 @ sk_A)
% 0.83/1.03          | (v2_struct_0 @ X0)
% 0.83/1.03          | ~ (v1_pre_topc @ X0)
% 0.83/1.03          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.03          | ((X0) = (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.83/1.03  thf('29', plain,
% 0.83/1.03      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.83/1.03        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['20', '28'])).
% 0.83/1.03  thf('30', plain,
% 0.83/1.03      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | ~ (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['29'])).
% 0.83/1.03  thf('31', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['15', '30'])).
% 0.83/1.03  thf('32', plain,
% 0.83/1.03      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | ~ (v1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['31'])).
% 0.83/1.03  thf('33', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['10', '32'])).
% 0.83/1.03  thf('34', plain,
% 0.83/1.03      (((v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['33'])).
% 0.83/1.03  thf('35', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('36', plain,
% 0.83/1.03      (![X27 : $i, X28 : $i]:
% 0.83/1.03         ((v1_xboole_0 @ X27)
% 0.83/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.83/1.03          | ~ (v2_struct_0 @ (sk_C_1 @ X27 @ X28))
% 0.83/1.03          | ~ (l1_pre_topc @ X28)
% 0.83/1.03          | (v2_struct_0 @ X28))),
% 0.83/1.03      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.83/1.03  thf('37', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/1.03  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('39', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['37', '38'])).
% 0.83/1.03  thf('40', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | ((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['34', '39'])).
% 0.83/1.03  thf('41', plain,
% 0.83/1.03      ((((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['40'])).
% 0.83/1.03  thf('42', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ((k1_tarski @ sk_B)
% 0.83/1.03            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['18', '19'])).
% 0.83/1.03  thf('43', plain,
% 0.83/1.03      ((((k1_tarski @ sk_B) = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['41', '42'])).
% 0.83/1.03  thf('44', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | ((k1_tarski @ sk_B) = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.83/1.03      inference('simplify', [status(thm)], ['43'])).
% 0.83/1.03  thf('45', plain,
% 0.83/1.03      ((((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['40'])).
% 0.83/1.03  thf('46', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.83/1.03  thf('47', plain,
% 0.83/1.03      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['45', '46'])).
% 0.83/1.03  thf('48', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.83/1.03      inference('simplify', [status(thm)], ['47'])).
% 0.83/1.03  thf('49', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.03  thf('50', plain,
% 0.83/1.03      ((((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['40'])).
% 0.83/1.03  thf('51', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (m1_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.83/1.03  thf(cc1_pre_topc, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.83/1.03  thf('52', plain,
% 0.83/1.03      (![X13 : $i, X14 : $i]:
% 0.83/1.03         (~ (m1_pre_topc @ X13 @ X14)
% 0.83/1.03          | (v2_pre_topc @ X13)
% 0.83/1.03          | ~ (l1_pre_topc @ X14)
% 0.83/1.03          | ~ (v2_pre_topc @ X14))),
% 0.83/1.03      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.83/1.03  thf('53', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | ~ (v2_pre_topc @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['51', '52'])).
% 0.83/1.03  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('56', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_pre_topc @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.83/1.03      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.83/1.03  thf('57', plain,
% 0.83/1.03      (((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['50', '56'])).
% 0.83/1.03  thf('58', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['57'])).
% 0.83/1.03  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(t24_tex_2, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.03           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.83/1.03             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.83/1.03               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.83/1.03  thf('60', plain,
% 0.83/1.03      (![X29 : $i, X30 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.83/1.03          | (v1_tdlat_3 @ (k1_tex_2 @ X30 @ X29))
% 0.83/1.03          | ~ (v2_pre_topc @ (k1_tex_2 @ X30 @ X29))
% 0.83/1.03          | ~ (l1_pre_topc @ X30)
% 0.83/1.03          | (v2_struct_0 @ X30))),
% 0.83/1.03      inference('cnf', [status(esa)], [t24_tex_2])).
% 0.83/1.03  thf('61', plain,
% 0.83/1.03      (((v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.83/1.03  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('63', plain,
% 0.83/1.03      (((v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/1.03  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('65', plain,
% 0.83/1.03      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('clc', [status(thm)], ['63', '64'])).
% 0.83/1.03  thf('66', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['58', '65'])).
% 0.83/1.03  thf('67', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | ((k1_tarski @ sk_B) = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.83/1.03      inference('simplify', [status(thm)], ['43'])).
% 0.83/1.03  thf(t26_tex_2, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.03       ( ![B:$i]:
% 0.83/1.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.83/1.03           ( ![C:$i]:
% 0.83/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.03               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.83/1.03                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.83/1.03  thf('68', plain,
% 0.83/1.03      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.83/1.03         ((v2_struct_0 @ X31)
% 0.83/1.03          | ~ (m1_pre_topc @ X31 @ X32)
% 0.83/1.03          | ((X33) != (u1_struct_0 @ X31))
% 0.83/1.03          | ~ (v1_tdlat_3 @ X31)
% 0.83/1.03          | (v2_tex_2 @ X33 @ X32)
% 0.83/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.83/1.03          | ~ (l1_pre_topc @ X32)
% 0.83/1.03          | (v2_struct_0 @ X32))),
% 0.83/1.03      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.83/1.03  thf('69', plain,
% 0.83/1.03      (![X31 : $i, X32 : $i]:
% 0.83/1.03         ((v2_struct_0 @ X32)
% 0.83/1.03          | ~ (l1_pre_topc @ X32)
% 0.83/1.03          | ~ (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.83/1.03               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.83/1.03          | (v2_tex_2 @ (u1_struct_0 @ X31) @ X32)
% 0.83/1.03          | ~ (v1_tdlat_3 @ X31)
% 0.83/1.03          | ~ (m1_pre_topc @ X31 @ X32)
% 0.83/1.03          | (v2_struct_0 @ X31))),
% 0.83/1.03      inference('simplify', [status(thm)], ['68'])).
% 0.83/1.03  thf('70', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.83/1.03          | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03          | (v2_struct_0 @ sk_A)
% 0.83/1.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.83/1.03          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0)
% 0.83/1.03          | ~ (l1_pre_topc @ X0)
% 0.83/1.03          | (v2_struct_0 @ X0))),
% 0.83/1.03      inference('sup-', [status(thm)], ['67', '69'])).
% 0.83/1.03  thf('71', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (v2_struct_0 @ sk_A)
% 0.83/1.03          | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03          | (v2_struct_0 @ X0)
% 0.83/1.03          | ~ (l1_pre_topc @ X0)
% 0.83/1.03          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0)
% 0.83/1.03          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.83/1.03          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03          | (v2_struct_0 @ sk_A)
% 0.83/1.03          | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03          | ~ (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.83/1.03      inference('sup-', [status(thm)], ['66', '70'])).
% 0.83/1.03  thf('72', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (~ (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.83/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.83/1.03          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.83/1.03          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0)
% 0.83/1.03          | ~ (l1_pre_topc @ X0)
% 0.83/1.03          | (v2_struct_0 @ X0)
% 0.83/1.03          | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03          | (v2_struct_0 @ sk_A)
% 0.83/1.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['71'])).
% 0.83/1.03  thf('73', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.03        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.83/1.03        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.83/1.03        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['49', '72'])).
% 0.83/1.03  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('75', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.83/1.03        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.83/1.03        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.83/1.03  thf('76', plain,
% 0.83/1.03      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.83/1.03        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['75'])).
% 0.83/1.03  thf('77', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.83/1.03        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['48', '76'])).
% 0.83/1.03  thf('78', plain,
% 0.83/1.03      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['77'])).
% 0.83/1.03  thf('79', plain,
% 0.83/1.03      (((v2_tex_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('sup+', [status(thm)], ['44', '78'])).
% 0.83/1.03  thf('80', plain,
% 0.83/1.03      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_tex_2 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.83/1.03      inference('simplify', [status(thm)], ['79'])).
% 0.83/1.03  thf('81', plain,
% 0.83/1.03      ((((sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['40'])).
% 0.83/1.03  thf('82', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (v2_struct_0 @ (sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('demod', [status(thm)], ['37', '38'])).
% 0.83/1.03  thf('83', plain,
% 0.83/1.03      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['81', '82'])).
% 0.83/1.03  thf('84', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | ~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['83'])).
% 0.83/1.03  thf('85', plain,
% 0.83/1.03      (((v2_tex_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['80', '84'])).
% 0.83/1.03  thf('86', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_tex_2 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.83/1.03      inference('simplify', [status(thm)], ['85'])).
% 0.83/1.03  thf('87', plain,
% 0.83/1.03      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.03  thf('88', plain,
% 0.83/1.03      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('89', plain,
% 0.83/1.03      ((~ (v2_tex_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['87', '88'])).
% 0.83/1.03  thf('90', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['86', '89'])).
% 0.83/1.03  thf('91', plain,
% 0.83/1.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.83/1.03      inference('simplify', [status(thm)], ['90'])).
% 0.83/1.03  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('93', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.03      inference('clc', [status(thm)], ['91', '92'])).
% 0.83/1.03  thf(fc2_struct_0, axiom,
% 0.83/1.03    (![A:$i]:
% 0.83/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.03       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.03  thf('94', plain,
% 0.83/1.03      (![X19 : $i]:
% 0.83/1.03         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.83/1.03          | ~ (l1_struct_0 @ X19)
% 0.83/1.03          | (v2_struct_0 @ X19))),
% 0.83/1.03      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.83/1.03  thf('95', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.83/1.03        | (v2_struct_0 @ sk_A)
% 0.83/1.03        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.03      inference('sup-', [status(thm)], ['93', '94'])).
% 0.83/1.03  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf(dt_l1_pre_topc, axiom,
% 0.83/1.03    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.83/1.03  thf('97', plain,
% 0.83/1.03      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.83/1.03      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.83/1.03  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.03      inference('sup-', [status(thm)], ['96', '97'])).
% 0.83/1.03  thf('99', plain,
% 0.83/1.03      (((v1_xboole_0 @ (k1_tarski @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.83/1.03      inference('demod', [status(thm)], ['95', '98'])).
% 0.83/1.03  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.03  thf('101', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.83/1.03      inference('clc', [status(thm)], ['99', '100'])).
% 0.83/1.03  thf('102', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.83/1.03      inference('simplify', [status(thm)], ['0'])).
% 0.83/1.03  thf('103', plain,
% 0.83/1.03      (![X6 : $i, X7 : $i]:
% 0.83/1.03         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.83/1.03          | ~ (r2_hidden @ X6 @ X7))),
% 0.83/1.03      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.83/1.03  thf('104', plain,
% 0.83/1.03      (![X0 : $i]:
% 0.83/1.03         (m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ (k1_tarski @ X0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['102', '103'])).
% 0.83/1.03  thf(t5_subset, axiom,
% 0.83/1.03    (![A:$i,B:$i,C:$i]:
% 0.83/1.03     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.83/1.03          ( v1_xboole_0 @ C ) ) ))).
% 0.83/1.03  thf('105', plain,
% 0.83/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.03         (~ (r2_hidden @ X10 @ X11)
% 0.83/1.03          | ~ (v1_xboole_0 @ X12)
% 0.83/1.03          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.83/1.03      inference('cnf', [status(esa)], [t5_subset])).
% 0.83/1.03  thf('106', plain,
% 0.83/1.03      (![X0 : $i, X1 : $i]:
% 0.83/1.03         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.83/1.03          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.83/1.03      inference('sup-', [status(thm)], ['104', '105'])).
% 0.83/1.03  thf('107', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))),
% 0.83/1.03      inference('sup-', [status(thm)], ['101', '106'])).
% 0.83/1.03  thf('108', plain, ($false), inference('sup-', [status(thm)], ['1', '107'])).
% 0.83/1.03  
% 0.83/1.03  % SZS output end Refutation
% 0.83/1.03  
% 0.83/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
