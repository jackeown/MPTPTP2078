%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Vj1cOVt6c

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:29 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 182 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   23
%              Number of atoms          : 1052 (3343 expanded)
%              Number of equality atoms :   16 (  69 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_tdlat_3 @ X22 )
      | ~ ( v4_pre_topc @ X23 @ X22 )
      | ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ X26 )
      | ( r1_xboole_0 @ X24 @ ( k2_pre_topc @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('44',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['41','51'])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

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

thf('54',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_hidden @ X27 @ ( k2_pre_topc @ X28 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X29 ) ) )
      | ( ( k2_pre_topc @ X28 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X27 ) )
        = ( k2_pre_topc @ X28 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v3_tdlat_3 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('69',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('72',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Vj1cOVt6c
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.67  % Solved by: fo/fo7.sh
% 0.44/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.67  % done 326 iterations in 0.209s
% 0.44/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.67  % SZS output start Refutation
% 0.44/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.67  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.44/0.67  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.44/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.67  thf(t56_tex_2, conjecture,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.44/0.67         ( l1_pre_topc @ A ) ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67               ( ( r1_xboole_0 @
% 0.44/0.67                   ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.44/0.67                   ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.44/0.67                 ( ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.44/0.67                   ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.67    (~( ![A:$i]:
% 0.44/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.67            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.67          ( ![B:$i]:
% 0.44/0.67            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67              ( ![C:$i]:
% 0.44/0.67                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67                  ( ( r1_xboole_0 @
% 0.44/0.67                      ( k2_pre_topc @
% 0.44/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.44/0.67                      ( k2_pre_topc @
% 0.44/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.44/0.67                    ( ( k2_pre_topc @
% 0.44/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.44/0.67                      ( k2_pre_topc @
% 0.44/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.44/0.67    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.44/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(t2_subset, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.44/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.67  thf('2', plain,
% 0.44/0.67      (![X9 : $i, X10 : $i]:
% 0.44/0.67         ((r2_hidden @ X9 @ X10)
% 0.44/0.67          | (v1_xboole_0 @ X10)
% 0.44/0.67          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.44/0.67  thf('3', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.67  thf(t63_subset_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( r2_hidden @ A @ B ) =>
% 0.44/0.67       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.44/0.67  thf('4', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.44/0.67          | ~ (r2_hidden @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.44/0.67  thf('5', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.44/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.67  thf(l27_zfmisc_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.44/0.67  thf('6', plain,
% 0.44/0.67      (![X3 : $i, X4 : $i]:
% 0.44/0.67         ((r1_xboole_0 @ (k1_tarski @ X3) @ X4) | (r2_hidden @ X3 @ X4))),
% 0.44/0.67      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.44/0.67  thf(symmetry_r1_xboole_0, axiom,
% 0.44/0.67    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.44/0.67  thf('7', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.67      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.44/0.67  thf('8', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.67  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('10', plain,
% 0.44/0.67      (![X9 : $i, X10 : $i]:
% 0.44/0.67         ((r2_hidden @ X9 @ X10)
% 0.44/0.67          | (v1_xboole_0 @ X10)
% 0.44/0.67          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.44/0.67  thf('11', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.67  thf('12', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.44/0.67          | ~ (r2_hidden @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.44/0.67  thf('13', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.44/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.67  thf(dt_k2_pre_topc, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( ( l1_pre_topc @ A ) & 
% 0.44/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.67       ( m1_subset_1 @
% 0.44/0.67         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.67  thf('14', plain,
% 0.44/0.67      (![X14 : $i, X15 : $i]:
% 0.44/0.67         (~ (l1_pre_topc @ X14)
% 0.44/0.67          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.67          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.44/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.44/0.67  thf('15', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.67  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('17', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.67      inference('demod', [status(thm)], ['15', '16'])).
% 0.44/0.67  thf(t24_tdlat_3, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.67       ( ( v3_tdlat_3 @ A ) <=>
% 0.44/0.67         ( ![B:$i]:
% 0.44/0.67           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.67  thf('18', plain,
% 0.44/0.67      (![X22 : $i, X23 : $i]:
% 0.44/0.67         (~ (v3_tdlat_3 @ X22)
% 0.44/0.67          | ~ (v4_pre_topc @ X23 @ X22)
% 0.44/0.67          | (v3_pre_topc @ X23 @ X22)
% 0.44/0.67          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.44/0.67          | ~ (l1_pre_topc @ X22)
% 0.44/0.67          | ~ (v2_pre_topc @ X22))),
% 0.44/0.67      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.44/0.67  thf('19', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.67        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.44/0.67        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.44/0.67        | ~ (v3_tdlat_3 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.67  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('22', plain, ((v3_tdlat_3 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.44/0.67        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.44/0.67      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.44/0.67  thf('24', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.44/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.67  thf(fc1_tops_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.44/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.67       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.44/0.67  thf('25', plain,
% 0.44/0.67      (![X20 : $i, X21 : $i]:
% 0.44/0.67         (~ (l1_pre_topc @ X20)
% 0.44/0.67          | ~ (v2_pre_topc @ X20)
% 0.44/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67          | (v4_pre_topc @ (k2_pre_topc @ X20 @ X21) @ X20))),
% 0.44/0.67      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.44/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.67  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('29', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.44/0.67      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.44/0.67  thf('30', plain,
% 0.44/0.67      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('clc', [status(thm)], ['23', '29'])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.67      inference('demod', [status(thm)], ['15', '16'])).
% 0.44/0.67  thf(t40_tsep_1, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.44/0.67                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf('32', plain,
% 0.44/0.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.67          | ~ (v3_pre_topc @ X24 @ X25)
% 0.44/0.67          | ~ (r1_xboole_0 @ X24 @ X26)
% 0.44/0.67          | (r1_xboole_0 @ X24 @ (k2_pre_topc @ X25 @ X26))
% 0.44/0.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.67          | ~ (l1_pre_topc @ X25)
% 0.44/0.67          | ~ (v2_pre_topc @ X25))),
% 0.44/0.67      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.44/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.44/0.67          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.67  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('36', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.44/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.44/0.67          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.44/0.67      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.44/0.67  thf('37', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.44/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['30', '36'])).
% 0.44/0.67  thf('38', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.44/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.44/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.44/0.67  thf('39', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.44/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.44/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['8', '38'])).
% 0.44/0.67  thf('40', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '39'])).
% 0.44/0.67  thf('41', plain,
% 0.44/0.67      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.44/0.67        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['40'])).
% 0.44/0.67  thf('42', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(redefinition_k6_domain_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.44/0.67       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.44/0.67  thf('43', plain,
% 0.44/0.67      (![X18 : $i, X19 : $i]:
% 0.44/0.67         ((v1_xboole_0 @ X18)
% 0.44/0.67          | ~ (m1_subset_1 @ X19 @ X18)
% 0.44/0.67          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.44/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.44/0.67  thf('44', plain,
% 0.44/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.67  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('46', plain,
% 0.44/0.67      (![X18 : $i, X19 : $i]:
% 0.44/0.67         ((v1_xboole_0 @ X18)
% 0.44/0.67          | ~ (m1_subset_1 @ X19 @ X18)
% 0.44/0.67          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.44/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.44/0.67  thf('47', plain,
% 0.44/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.67  thf('48', plain,
% 0.44/0.67      (~ (r1_xboole_0 @ 
% 0.44/0.67          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.44/0.67          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('49', plain,
% 0.44/0.67      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.67  thf('50', plain,
% 0.44/0.67      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['44', '49'])).
% 0.44/0.67  thf('51', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.44/0.67             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.44/0.67      inference('simplify', [status(thm)], ['50'])).
% 0.44/0.67  thf('52', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.44/0.67      inference('clc', [status(thm)], ['41', '51'])).
% 0.44/0.67  thf('53', plain,
% 0.44/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.67  thf(t55_tex_2, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.44/0.67         ( l1_pre_topc @ A ) ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67               ( ( r2_hidden @
% 0.44/0.67                   B @ 
% 0.44/0.67                   ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.44/0.67                 ( ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.44/0.67                   ( k2_pre_topc @
% 0.44/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf('54', plain,
% 0.44/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.44/0.67          | ~ (r2_hidden @ X27 @ 
% 0.44/0.67               (k2_pre_topc @ X28 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X29)))
% 0.44/0.67          | ((k2_pre_topc @ X28 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X27))
% 0.44/0.67              = (k2_pre_topc @ X28 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X29)))
% 0.44/0.67          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.44/0.67          | ~ (l1_pre_topc @ X28)
% 0.44/0.67          | ~ (v3_tdlat_3 @ X28)
% 0.44/0.67          | ~ (v2_pre_topc @ X28)
% 0.44/0.67          | (v2_struct_0 @ X28))),
% 0.44/0.67      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.44/0.67  thf('55', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.44/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | (v2_struct_0 @ sk_A)
% 0.44/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.67          | ~ (v3_tdlat_3 @ sk_A)
% 0.44/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.67          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.44/0.67              = (k2_pre_topc @ sk_A @ 
% 0.44/0.67                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.67  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('57', plain, ((v3_tdlat_3 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('60', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.44/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | (v2_struct_0 @ sk_A)
% 0.44/0.67          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.44/0.67              = (k2_pre_topc @ sk_A @ 
% 0.44/0.67                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.44/0.67  thf('61', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.44/0.67            = (k2_pre_topc @ sk_A @ 
% 0.44/0.67               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.44/0.67        | (v2_struct_0 @ sk_A)
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['52', '60'])).
% 0.44/0.67  thf('62', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('63', plain,
% 0.44/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.44/0.67            = (k2_pre_topc @ sk_A @ 
% 0.44/0.67               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.44/0.67        | (v2_struct_0 @ sk_A)
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('demod', [status(thm)], ['61', '62'])).
% 0.44/0.67  thf('64', plain,
% 0.44/0.67      (((v2_struct_0 @ sk_A)
% 0.44/0.67        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.44/0.67            = (k2_pre_topc @ sk_A @ 
% 0.44/0.67               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.44/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['63'])).
% 0.44/0.67  thf('65', plain,
% 0.44/0.67      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.44/0.67         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('66', plain,
% 0.44/0.67      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.44/0.67  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('68', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('clc', [status(thm)], ['66', '67'])).
% 0.44/0.67  thf(fc2_struct_0, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.44/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.67  thf('69', plain,
% 0.44/0.67      (![X17 : $i]:
% 0.44/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.44/0.67          | ~ (l1_struct_0 @ X17)
% 0.44/0.67          | (v2_struct_0 @ X17))),
% 0.44/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.44/0.67  thf('70', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.67  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(dt_l1_pre_topc, axiom,
% 0.44/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.67  thf('72', plain,
% 0.44/0.67      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.67  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.67      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.67  thf('74', plain, ((v2_struct_0 @ sk_A)),
% 0.44/0.67      inference('demod', [status(thm)], ['70', '73'])).
% 0.44/0.67  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.44/0.67  
% 0.44/0.67  % SZS output end Refutation
% 0.44/0.67  
% 0.44/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
