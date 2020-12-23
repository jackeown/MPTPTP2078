%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MezD2gSqCP

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:29 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 206 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   24
%              Number of atoms          : 1172 (3810 expanded)
%              Number of equality atoms :   25 (  84 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
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
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != X18 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k2_pre_topc @ X16 @ X17 ) )
        = ( k2_pre_topc @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ X26 )
      | ( r1_xboole_0 @ X24 @ ( k2_pre_topc @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['5','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('50',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['47','57'])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

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

thf('60',plain,(
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

thf('61',plain,(
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
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('78',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MezD2gSqCP
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 288 iterations in 0.188s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.46/0.64  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(t56_tex_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.64         ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64               ( ( r1_xboole_0 @
% 0.46/0.64                   ( k2_pre_topc @
% 0.46/0.64                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.46/0.64                   ( k2_pre_topc @
% 0.46/0.64                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.46/0.64                 ( ( k2_pre_topc @
% 0.46/0.64                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.46/0.64                   ( k2_pre_topc @
% 0.46/0.64                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.65            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65                  ( ( r1_xboole_0 @
% 0.46/0.65                      ( k2_pre_topc @
% 0.46/0.65                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.46/0.65                      ( k2_pre_topc @
% 0.46/0.65                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.46/0.65                    ( ( k2_pre_topc @
% 0.46/0.65                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.46/0.65                      ( k2_pre_topc @
% 0.46/0.65                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.46/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t2_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.65       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         ((r2_hidden @ X10 @ X11)
% 0.46/0.65          | (v1_xboole_0 @ X11)
% 0.46/0.65          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf(t63_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.46/0.65          | ~ (r2_hidden @ X8 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf(l27_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ (k1_tarski @ X6) @ X7) | (r2_hidden @ X6 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.65  thf(symmetry_r1_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('9', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         ((r2_hidden @ X10 @ X11)
% 0.46/0.65          | (v1_xboole_0 @ X11)
% 0.46/0.65          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.46/0.65          | ~ (r2_hidden @ X8 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf(dt_k2_pre_topc, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65       ( m1_subset_1 @
% 0.46/0.65         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X12)
% 0.46/0.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.65          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf(t24_tdlat_3, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ( v3_tdlat_3 @ A ) <=>
% 0.46/0.65         ( ![B:$i]:
% 0.46/0.65           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (v3_tdlat_3 @ X22)
% 0.46/0.65          | ~ (v4_pre_topc @ X23 @ X22)
% 0.46/0.65          | (v3_pre_topc @ X23 @ X22)
% 0.46/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.65          | ~ (l1_pre_topc @ X22)
% 0.46/0.65          | ~ (v2_pre_topc @ X22))),
% 0.46/0.65      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | ~ (v3_tdlat_3 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf(t52_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.65             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.65               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.65          | ~ (v2_pre_topc @ X19)
% 0.46/0.65          | ((k2_pre_topc @ X19 @ X18) != (X18))
% 0.46/0.65          | (v4_pre_topc @ X18 @ X19)
% 0.46/0.65          | ~ (l1_pre_topc @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.46/0.65      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k1_tarski @ sk_B_2) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf(projectivity_k2_pre_topc, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.46/0.65         ( k2_pre_topc @ A @ B ) ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X16)
% 0.46/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.65          | ((k2_pre_topc @ X16 @ (k2_pre_topc @ X16 @ X17))
% 0.46/0.65              = (k2_pre_topc @ X16 @ X17)))),
% 0.46/0.65      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.46/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['29', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['23', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf(t40_tsep_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.46/0.65                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.65          | ~ (v3_pre_topc @ X24 @ X25)
% 0.46/0.65          | ~ (r1_xboole_0 @ X24 @ X26)
% 0.46/0.65          | (r1_xboole_0 @ X24 @ (k2_pre_topc @ X25 @ X26))
% 0.46/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.65          | ~ (l1_pre_topc @ X25)
% 0.46/0.65          | ~ (v2_pre_topc @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.65          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.46/0.65          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.65          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.46/0.65          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.46/0.65          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['36', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.65          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.46/0.65          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.65  thf('48', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X20)
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ X20)
% 0.46/0.65          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X20)
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ X20)
% 0.46/0.65          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (~ (r1_xboole_0 @ 
% 0.46/0.65          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.46/0.65      inference('clc', [status(thm)], ['47', '57'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf(t55_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.65         ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65               ( ( r2_hidden @
% 0.46/0.65                   B @ 
% 0.46/0.65                   ( k2_pre_topc @
% 0.46/0.65                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.46/0.65                 ( ( k2_pre_topc @
% 0.46/0.65                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.46/0.65                   ( k2_pre_topc @
% 0.46/0.65                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.46/0.65          | ~ (r2_hidden @ X27 @ 
% 0.46/0.65               (k2_pre_topc @ X28 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X29)))
% 0.46/0.65          | ((k2_pre_topc @ X28 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X27))
% 0.46/0.65              = (k2_pre_topc @ X28 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X29)))
% 0.46/0.65          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.46/0.65          | ~ (l1_pre_topc @ X28)
% 0.46/0.65          | ~ (v3_tdlat_3 @ X28)
% 0.46/0.65          | ~ (v2_pre_topc @ X28)
% 0.46/0.65          | (v2_struct_0 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65          | ~ (v3_tdlat_3 @ sk_A)
% 0.46/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.46/0.65              = (k2_pre_topc @ sk_A @ 
% 0.46/0.65                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.65  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('63', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('65', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_2)))
% 0.46/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.46/0.65              = (k2_pre_topc @ sk_A @ 
% 0.46/0.65                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.46/0.65            = (k2_pre_topc @ sk_A @ 
% 0.46/0.65               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['58', '66'])).
% 0.46/0.65  thf('68', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.46/0.65            = (k2_pre_topc @ sk_A @ 
% 0.46/0.65               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.46/0.65            = (k2_pre_topc @ sk_A @ 
% 0.46/0.65               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.46/0.65  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('74', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf(fc2_struct_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (![X15 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.46/0.65          | ~ (l1_struct_0 @ X15)
% 0.46/0.65          | (v2_struct_0 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.65  thf('76', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.65  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_l1_pre_topc, axiom,
% 0.46/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.65  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['76', '79'])).
% 0.46/0.65  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
