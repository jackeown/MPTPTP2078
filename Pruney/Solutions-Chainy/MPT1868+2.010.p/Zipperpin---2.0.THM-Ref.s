%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1cSnI44zis

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:40 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 254 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   22
%              Number of atoms          :  840 (2806 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('11',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k1_tex_2 @ X12 @ X11 ) )
      | ( ( u1_struct_0 @ X13 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( v1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) @ X12 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('24',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('32',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

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

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tdlat_3 @ X18 )
      | ( v2_tex_2 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tdlat_3 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( v1_tdlat_3 @ ( k1_tex_2 @ X17 @ X16 ) )
      | ~ ( v2_pre_topc @ ( k1_tex_2 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tex_2])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('52',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','59'])).

thf('61',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('74',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1cSnI44zis
% 0.15/0.37  % Computer   : n008.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 12:28:15 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 60 iterations in 0.042s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.35/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.35/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.53  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.35/0.53  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.35/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(t36_tex_2, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.53            ( l1_pre_topc @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.35/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t2_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         ((r2_hidden @ X3 @ X4)
% 0.35/0.53          | (v1_xboole_0 @ X4)
% 0.35/0.53          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf(t63_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.35/0.53       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i]:
% 0.35/0.53         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.35/0.53          | ~ (r2_hidden @ X1 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ X9)
% 0.35/0.53          | ~ (m1_subset_1 @ X10 @ X9)
% 0.35/0.53          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_k1_tex_2, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.35/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.35/0.53         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.35/0.53         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (l1_pre_topc @ X14)
% 0.35/0.53          | (v2_struct_0 @ X14)
% 0.35/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.35/0.53          | (v1_pre_topc @ (k1_tex_2 @ X14 @ X15)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('15', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf(d4_tex_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.35/0.53                 ( m1_pre_topc @ C @ A ) ) =>
% 0.35/0.53               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.35/0.53                 ( ( u1_struct_0 @ C ) =
% 0.35/0.53                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.35/0.53          | ((X13) != (k1_tex_2 @ X12 @ X11))
% 0.35/0.53          | ((u1_struct_0 @ X13) = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.35/0.53          | ~ (m1_pre_topc @ X13 @ X12)
% 0.35/0.53          | ~ (v1_pre_topc @ X13)
% 0.35/0.53          | (v2_struct_0 @ X13)
% 0.35/0.53          | ~ (l1_pre_topc @ X12)
% 0.35/0.53          | (v2_struct_0 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X11 : $i, X12 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X12)
% 0.35/0.53          | ~ (l1_pre_topc @ X12)
% 0.35/0.53          | (v2_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.35/0.53          | ~ (v1_pre_topc @ (k1_tex_2 @ X12 @ X11))
% 0.35/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ X12 @ X11) @ X12)
% 0.35/0.53          | ((u1_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.35/0.53              = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.35/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['15', '17'])).
% 0.35/0.53  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.35/0.53  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (l1_pre_topc @ X14)
% 0.35/0.53          | (v2_struct_0 @ X14)
% 0.35/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.35/0.53          | (m1_pre_topc @ (k1_tex_2 @ X14 @ X15) @ X14))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.53  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('28', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.35/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['21', '28'])).
% 0.35/0.53  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (l1_pre_topc @ X14)
% 0.35/0.53          | (v2_struct_0 @ X14)
% 0.35/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.35/0.53          | ~ (v2_struct_0 @ (k1_tex_2 @ X14 @ X15)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.53  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('36', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('clc', [status(thm)], ['29', '36'])).
% 0.35/0.53  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf(t26_tex_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.35/0.53                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X18)
% 0.35/0.53          | ~ (m1_pre_topc @ X18 @ X19)
% 0.35/0.53          | ((X20) != (u1_struct_0 @ X18))
% 0.35/0.53          | ~ (v1_tdlat_3 @ X18)
% 0.35/0.53          | (v2_tex_2 @ X20 @ X19)
% 0.35/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.35/0.53          | ~ (l1_pre_topc @ X19)
% 0.35/0.53          | (v2_struct_0 @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X19)
% 0.35/0.53          | ~ (l1_pre_topc @ X19)
% 0.35/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.35/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.35/0.53          | (v2_tex_2 @ (u1_struct_0 @ X18) @ X19)
% 0.35/0.53          | ~ (v1_tdlat_3 @ X18)
% 0.35/0.53          | ~ (m1_pre_topc @ X18 @ X19)
% 0.35/0.53          | (v2_struct_0 @ X18))),
% 0.35/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.35/0.53          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0)
% 0.35/0.53          | ~ (l1_pre_topc @ X0)
% 0.35/0.53          | (v2_struct_0 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.35/0.53  thf('43', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t24_tex_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.35/0.53             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.35/0.53               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.35/0.53          | (v1_tdlat_3 @ (k1_tex_2 @ X17 @ X16))
% 0.35/0.53          | ~ (v2_pre_topc @ (k1_tex_2 @ X17 @ X16))
% 0.35/0.53          | ~ (l1_pre_topc @ X17)
% 0.35/0.53          | (v2_struct_0 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [t24_tex_2])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.53  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['45', '46'])).
% 0.35/0.53  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.35/0.53  thf('50', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.35/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf(cc1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ X5 @ X6)
% 0.35/0.53          | (v2_pre_topc @ X5)
% 0.35/0.53          | ~ (l1_pre_topc @ X6)
% 0.35/0.53          | ~ (v2_pre_topc @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.53  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('55', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.35/0.53  thf('56', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['49', '55'])).
% 0.35/0.53  thf('57', plain,
% 0.35/0.53      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf('58', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.35/0.53          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.35/0.53          | ~ (l1_pre_topc @ X0)
% 0.35/0.53          | (v2_struct_0 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['42', '56', '57'])).
% 0.35/0.53  thf('59', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | (v2_struct_0 @ X0)
% 0.35/0.53          | ~ (l1_pre_topc @ X0)
% 0.35/0.53          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.35/0.53          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.35/0.53          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['8', '58'])).
% 0.35/0.53  thf('60', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.35/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '59'])).
% 0.35/0.53  thf('61', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.35/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('63', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.35/0.53  thf('64', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['63'])).
% 0.35/0.53  thf('65', plain,
% 0.35/0.53      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('66', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.35/0.53  thf('67', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('68', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('clc', [status(thm)], ['66', '67'])).
% 0.35/0.53  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('70', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('clc', [status(thm)], ['68', '69'])).
% 0.35/0.53  thf(fc2_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.53  thf('71', plain,
% 0.35/0.53      (![X8 : $i]:
% 0.35/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.35/0.53          | ~ (l1_struct_0 @ X8)
% 0.35/0.53          | (v2_struct_0 @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.53  thf('72', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.35/0.53  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_l1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('74', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.53  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.35/0.53  thf('76', plain, ((v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('demod', [status(thm)], ['72', '75'])).
% 0.35/0.53  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
