%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XaxjSoC44I

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:28 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 199 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   24
%              Number of atoms          : 1129 (3645 expanded)
%              Number of equality atoms :   51 ( 121 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('11',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('21',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 )
      | ( r1_xboole_0 @ X21 @ ( k2_pre_topc @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('41',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('44',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('52',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

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

thf('57',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k2_pre_topc @ X25 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X26 ) ) )
      | ( ( k2_pre_topc @ X25 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) )
        = ( k2_pre_topc @ X25 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v3_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','71'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('77',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['74','75','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XaxjSoC44I
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 579 iterations in 0.441s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.89  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.68/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.68/0.89  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.68/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.89  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.68/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.89  thf(t56_tex_2, conjecture,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.68/0.89         ( l1_pre_topc @ A ) ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89           ( ![C:$i]:
% 0.68/0.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89               ( ( r1_xboole_0 @
% 0.68/0.89                   ( k2_pre_topc @
% 0.68/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.68/0.89                   ( k2_pre_topc @
% 0.68/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.68/0.89                 ( ( k2_pre_topc @
% 0.68/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.68/0.89                   ( k2_pre_topc @
% 0.68/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i]:
% 0.68/0.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.89            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.89          ( ![B:$i]:
% 0.68/0.89            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89              ( ![C:$i]:
% 0.68/0.89                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.89                  ( ( r1_xboole_0 @
% 0.68/0.89                      ( k2_pre_topc @
% 0.68/0.89                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.68/0.89                      ( k2_pre_topc @
% 0.68/0.89                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.68/0.89                    ( ( k2_pre_topc @
% 0.68/0.89                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.68/0.89                      ( k2_pre_topc @
% 0.68/0.89                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.68/0.89  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t55_subset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ B @ A ) =>
% 0.68/0.89       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i]:
% 0.68/0.89         (((X5) = (k1_xboole_0))
% 0.68/0.89          | ~ (m1_subset_1 @ X6 @ X5)
% 0.68/0.89          | (m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.68/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.89  thf(t56_zfmisc_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (![X3 : $i, X4 : $i]:
% 0.68/0.89         ((r1_xboole_0 @ (k1_tarski @ X3) @ X4) | (r2_hidden @ X3 @ X4))),
% 0.68/0.89      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 0.68/0.89  thf(symmetry_r1_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.68/0.89      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i]:
% 0.68/0.89         (((X5) = (k1_xboole_0))
% 0.68/0.89          | ~ (m1_subset_1 @ X6 @ X5)
% 0.68/0.89          | (m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.68/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.89  thf(fc1_tops_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.68/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.89       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]:
% 0.68/0.89         (~ (l1_pre_topc @ X17)
% 0.68/0.89          | ~ (v2_pre_topc @ X17)
% 0.68/0.89          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.89          | (v4_pre_topc @ (k2_pre_topc @ X17 @ X18) @ X17))),
% 0.68/0.89      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.89  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.68/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.89  thf(dt_k2_pre_topc, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.89       ( m1_subset_1 @
% 0.68/0.89         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (l1_pre_topc @ X9)
% 0.68/0.89          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.68/0.89          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.68/0.89             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.89           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.89           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.89  thf(t24_tdlat_3, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.89       ( ( v3_tdlat_3 @ A ) <=>
% 0.68/0.89         ( ![B:$i]:
% 0.68/0.89           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.89             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (![X19 : $i, X20 : $i]:
% 0.68/0.89         (~ (v3_tdlat_3 @ X19)
% 0.68/0.89          | ~ (v4_pre_topc @ X20 @ X19)
% 0.68/0.89          | (v3_pre_topc @ X20 @ X19)
% 0.68/0.89          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.68/0.89          | ~ (l1_pre_topc @ X19)
% 0.68/0.89          | ~ (v2_pre_topc @ X19))),
% 0.68/0.89      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.89        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.89        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.89        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.89        | ~ (v3_tdlat_3 @ sk_A))),
% 0.68/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.89  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('24', plain, ((v3_tdlat_3 @ sk_A)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('25', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.89        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['14', '25'])).
% 0.73/0.89  thf('27', plain,
% 0.73/0.89      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('simplify', [status(thm)], ['26'])).
% 0.73/0.89  thf('28', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.73/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.73/0.89  thf(t40_tsep_1, axiom,
% 0.73/0.89    (![A:$i]:
% 0.73/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.73/0.89       ( ![B:$i]:
% 0.73/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.73/0.89           ( ![C:$i]:
% 0.73/0.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.73/0.89               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.73/0.89                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.73/0.89  thf('29', plain,
% 0.73/0.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.73/0.89         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.73/0.89          | ~ (v3_pre_topc @ X21 @ X22)
% 0.73/0.89          | ~ (r1_xboole_0 @ X21 @ X23)
% 0.73/0.89          | (r1_xboole_0 @ X21 @ (k2_pre_topc @ X22 @ X23))
% 0.73/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.73/0.89          | ~ (l1_pre_topc @ X22)
% 0.73/0.89          | ~ (v2_pre_topc @ X22))),
% 0.73/0.89      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.73/0.89  thf('30', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89          | ~ (v2_pre_topc @ sk_A)
% 0.73/0.89          | ~ (l1_pre_topc @ sk_A)
% 0.73/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.73/0.89          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89             (k2_pre_topc @ sk_A @ X0))
% 0.73/0.89          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.73/0.89          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.73/0.89      inference('sup-', [status(thm)], ['28', '29'])).
% 0.73/0.89  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('33', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.73/0.89          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89             (k2_pre_topc @ sk_A @ X0))
% 0.73/0.89          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.73/0.89          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.73/0.89      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.73/0.89  thf('34', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.73/0.89          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89             (k2_pre_topc @ sk_A @ X0))
% 0.73/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.73/0.89          | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['27', '33'])).
% 0.73/0.89  thf('35', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.73/0.89          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89             (k2_pre_topc @ sk_A @ X0))
% 0.73/0.89          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.73/0.89          | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('simplify', [status(thm)], ['34'])).
% 0.73/0.89  thf('36', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.73/0.89          | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.73/0.89          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.73/0.89               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.73/0.89      inference('sup-', [status(thm)], ['6', '35'])).
% 0.73/0.89  thf('37', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.73/0.89      inference('sup-', [status(thm)], ['3', '36'])).
% 0.73/0.89  thf('38', plain,
% 0.73/0.89      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.73/0.89        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('simplify', [status(thm)], ['37'])).
% 0.73/0.89  thf('39', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf(redefinition_k6_domain_1, axiom,
% 0.73/0.89    (![A:$i,B:$i]:
% 0.73/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.73/0.89       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.73/0.89  thf('40', plain,
% 0.73/0.89      (![X15 : $i, X16 : $i]:
% 0.73/0.89         ((v1_xboole_0 @ X15)
% 0.73/0.89          | ~ (m1_subset_1 @ X16 @ X15)
% 0.73/0.89          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.73/0.89      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.73/0.89  thf('41', plain,
% 0.73/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.73/0.89  thf('42', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('43', plain,
% 0.73/0.89      (![X15 : $i, X16 : $i]:
% 0.73/0.89         ((v1_xboole_0 @ X15)
% 0.73/0.89          | ~ (m1_subset_1 @ X16 @ X15)
% 0.73/0.89          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.73/0.89      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.73/0.89  thf('44', plain,
% 0.73/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.73/0.89  thf('45', plain,
% 0.73/0.89      (~ (r1_xboole_0 @ 
% 0.73/0.89          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.73/0.89          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('46', plain,
% 0.73/0.89      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.73/0.89  thf('47', plain,
% 0.73/0.89      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['41', '46'])).
% 0.73/0.89  thf('48', plain,
% 0.73/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.73/0.89             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.73/0.89      inference('simplify', [status(thm)], ['47'])).
% 0.73/0.89  thf('49', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['38', '48'])).
% 0.73/0.89  thf('50', plain,
% 0.73/0.89      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.73/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.73/0.89  thf(cc1_subset_1, axiom,
% 0.73/0.89    (![A:$i]:
% 0.73/0.89     ( ( v1_xboole_0 @ A ) =>
% 0.73/0.89       ( ![B:$i]:
% 0.73/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.73/0.89  thf('51', plain,
% 0.73/0.89      (![X7 : $i, X8 : $i]:
% 0.73/0.89         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.73/0.89          | (v1_xboole_0 @ X7)
% 0.73/0.89          | ~ (v1_xboole_0 @ X8))),
% 0.73/0.89      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.73/0.89  thf('52', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['50', '51'])).
% 0.73/0.89  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.73/0.89  thf('53', plain, (![X2 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X2))),
% 0.73/0.89      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.73/0.89  thf('54', plain,
% 0.73/0.89      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.73/0.89  thf('55', plain,
% 0.73/0.89      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('clc', [status(thm)], ['49', '54'])).
% 0.73/0.89  thf('56', plain,
% 0.73/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.73/0.89  thf(t55_tex_2, axiom,
% 0.73/0.89    (![A:$i]:
% 0.73/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.73/0.89         ( l1_pre_topc @ A ) ) =>
% 0.73/0.89       ( ![B:$i]:
% 0.73/0.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.89           ( ![C:$i]:
% 0.73/0.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.73/0.89               ( ( r2_hidden @
% 0.73/0.89                   B @ 
% 0.73/0.89                   ( k2_pre_topc @
% 0.73/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.73/0.89                 ( ( k2_pre_topc @
% 0.73/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.73/0.89                   ( k2_pre_topc @
% 0.73/0.89                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.73/0.89  thf('57', plain,
% 0.73/0.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.73/0.89         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.73/0.89          | ~ (r2_hidden @ X24 @ 
% 0.73/0.89               (k2_pre_topc @ X25 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X26)))
% 0.73/0.89          | ((k2_pre_topc @ X25 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24))
% 0.73/0.89              = (k2_pre_topc @ X25 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X26)))
% 0.73/0.89          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.73/0.89          | ~ (l1_pre_topc @ X25)
% 0.73/0.89          | ~ (v3_tdlat_3 @ X25)
% 0.73/0.89          | ~ (v2_pre_topc @ X25)
% 0.73/0.89          | (v2_struct_0 @ X25))),
% 0.73/0.89      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.73/0.89  thf('58', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.73/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89          | (v2_struct_0 @ sk_A)
% 0.73/0.89          | ~ (v2_pre_topc @ sk_A)
% 0.73/0.89          | ~ (v3_tdlat_3 @ sk_A)
% 0.73/0.89          | ~ (l1_pre_topc @ sk_A)
% 0.73/0.89          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.73/0.89          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.73/0.89              = (k2_pre_topc @ sk_A @ 
% 0.73/0.89                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.73/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.73/0.89  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('60', plain, ((v3_tdlat_3 @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('62', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('63', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.73/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89          | (v2_struct_0 @ sk_A)
% 0.73/0.89          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.73/0.89              = (k2_pre_topc @ sk_A @ 
% 0.73/0.89                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.73/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.73/0.89  thf('64', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.73/0.89            = (k2_pre_topc @ sk_A @ 
% 0.73/0.89               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.73/0.89        | (v2_struct_0 @ sk_A)
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['55', '63'])).
% 0.73/0.89  thf('65', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('66', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.73/0.89            = (k2_pre_topc @ sk_A @ 
% 0.73/0.89               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.73/0.89        | (v2_struct_0 @ sk_A)
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('demod', [status(thm)], ['64', '65'])).
% 0.73/0.89  thf('67', plain,
% 0.73/0.89      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.73/0.89         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('68', plain,
% 0.73/0.89      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.73/0.89        | (v2_struct_0 @ sk_A)
% 0.73/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.73/0.89      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.73/0.89  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf('70', plain,
% 0.73/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('clc', [status(thm)], ['68', '69'])).
% 0.73/0.89  thf('71', plain,
% 0.73/0.89      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.73/0.89        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.73/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.73/0.89  thf('72', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.73/0.89      inference('clc', [status(thm)], ['70', '71'])).
% 0.73/0.89  thf(fc2_struct_0, axiom,
% 0.73/0.89    (![A:$i]:
% 0.73/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.73/0.89       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.73/0.89  thf('73', plain,
% 0.73/0.89      (![X12 : $i]:
% 0.73/0.89         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.73/0.89          | ~ (l1_struct_0 @ X12)
% 0.73/0.89          | (v2_struct_0 @ X12))),
% 0.73/0.89      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.73/0.89  thf('74', plain,
% 0.73/0.89      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.73/0.89        | (v2_struct_0 @ sk_A)
% 0.73/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.73/0.89      inference('sup-', [status(thm)], ['72', '73'])).
% 0.73/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.73/0.89  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.73/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.73/0.89  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf(dt_l1_pre_topc, axiom,
% 0.73/0.89    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.73/0.89  thf('77', plain,
% 0.73/0.89      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.73/0.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.73/0.89  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.73/0.89      inference('sup-', [status(thm)], ['76', '77'])).
% 0.73/0.89  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 0.73/0.89      inference('demod', [status(thm)], ['74', '75', '78'])).
% 0.73/0.89  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.73/0.89  
% 0.73/0.89  % SZS output end Refutation
% 0.73/0.89  
% 0.73/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
