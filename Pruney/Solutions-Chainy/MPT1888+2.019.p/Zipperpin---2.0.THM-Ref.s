%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZrklYbgk2E

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:30 EST 2020

% Result     : Theorem 16.61s
% Output     : Refutation 16.61s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 169 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          : 1226 (3154 expanded)
%              Number of equality atoms :   25 (  71 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('17',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k2_pre_topc @ X18 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X19 ) ) )
      | ( ( k2_pre_topc @ X18 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X17 ) )
        = ( k2_pre_topc @ X18 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('44',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k2_pre_topc @ X18 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X19 ) ) )
      | ( ( k2_pre_topc @ X18 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X17 ) )
        = ( k2_pre_topc @ X18 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('69',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('70',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['67','73'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZrklYbgk2E
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:31 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 16.61/16.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.61/16.86  % Solved by: fo/fo7.sh
% 16.61/16.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.61/16.86  % done 7173 iterations in 16.412s
% 16.61/16.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.61/16.86  % SZS output start Refutation
% 16.61/16.86  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 16.61/16.86  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 16.61/16.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 16.61/16.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 16.61/16.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 16.61/16.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.61/16.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 16.61/16.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 16.61/16.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 16.61/16.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 16.61/16.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 16.61/16.86  thf(sk_A_type, type, sk_A: $i).
% 16.61/16.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 16.61/16.86  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 16.61/16.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 16.61/16.86  thf(sk_B_type, type, sk_B: $i).
% 16.61/16.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 16.61/16.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.61/16.86  thf(t56_tex_2, conjecture,
% 16.61/16.86    (![A:$i]:
% 16.61/16.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 16.61/16.86         ( l1_pre_topc @ A ) ) =>
% 16.61/16.86       ( ![B:$i]:
% 16.61/16.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.61/16.86           ( ![C:$i]:
% 16.61/16.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 16.61/16.86               ( ( r1_xboole_0 @
% 16.61/16.86                   ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 16.61/16.86                   ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 16.61/16.86                 ( ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 16.61/16.86                   ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 16.61/16.86  thf(zf_stmt_0, negated_conjecture,
% 16.61/16.86    (~( ![A:$i]:
% 16.61/16.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 16.61/16.86            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.61/16.86          ( ![B:$i]:
% 16.61/16.86            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.61/16.86              ( ![C:$i]:
% 16.61/16.86                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 16.61/16.86                  ( ( r1_xboole_0 @
% 16.61/16.86                      ( k2_pre_topc @
% 16.61/16.86                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 16.61/16.86                      ( k2_pre_topc @
% 16.61/16.86                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 16.61/16.86                    ( ( k2_pre_topc @
% 16.61/16.86                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 16.61/16.86                      ( k2_pre_topc @
% 16.61/16.86                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 16.61/16.86    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 16.61/16.86  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 16.61/16.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.86  thf(t3_xboole_0, axiom,
% 16.61/16.86    (![A:$i,B:$i]:
% 16.61/16.86     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 16.61/16.86            ( r1_xboole_0 @ A @ B ) ) ) & 
% 16.61/16.86       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 16.61/16.86            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 16.61/16.86  thf('1', plain,
% 16.61/16.86      (![X0 : $i, X1 : $i]:
% 16.61/16.86         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 16.61/16.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.86  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 16.61/16.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.86  thf(t2_subset, axiom,
% 16.61/16.86    (![A:$i,B:$i]:
% 16.61/16.86     ( ( m1_subset_1 @ A @ B ) =>
% 16.61/16.86       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 16.61/16.86  thf('3', plain,
% 16.61/16.86      (![X6 : $i, X7 : $i]:
% 16.61/16.86         ((r2_hidden @ X6 @ X7)
% 16.61/16.86          | (v1_xboole_0 @ X7)
% 16.61/16.86          | ~ (m1_subset_1 @ X6 @ X7))),
% 16.61/16.86      inference('cnf', [status(esa)], [t2_subset])).
% 16.61/16.86  thf('4', plain,
% 16.61/16.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 16.61/16.86      inference('sup-', [status(thm)], ['2', '3'])).
% 16.61/16.86  thf(t63_subset_1, axiom,
% 16.61/16.86    (![A:$i,B:$i]:
% 16.61/16.86     ( ( r2_hidden @ A @ B ) =>
% 16.61/16.86       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 16.61/16.86  thf('5', plain,
% 16.61/16.86      (![X4 : $i, X5 : $i]:
% 16.61/16.86         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 16.61/16.86          | ~ (r2_hidden @ X4 @ X5))),
% 16.61/16.86      inference('cnf', [status(esa)], [t63_subset_1])).
% 16.61/16.86  thf('6', plain,
% 16.61/16.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 16.61/16.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.61/16.86      inference('sup-', [status(thm)], ['4', '5'])).
% 16.61/16.86  thf(dt_k2_pre_topc, axiom,
% 16.61/16.86    (![A:$i,B:$i]:
% 16.61/16.86     ( ( ( l1_pre_topc @ A ) & 
% 16.61/16.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.61/16.86       ( m1_subset_1 @
% 16.61/16.86         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 16.61/16.86  thf('7', plain,
% 16.61/16.86      (![X11 : $i, X12 : $i]:
% 16.61/16.86         (~ (l1_pre_topc @ X11)
% 16.61/16.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 16.61/16.86          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 16.61/16.86             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 16.61/16.86      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 16.61/16.86  thf('8', plain,
% 16.61/16.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ 
% 16.61/16.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.61/16.86        | ~ (l1_pre_topc @ sk_A))),
% 16.61/16.86      inference('sup-', [status(thm)], ['6', '7'])).
% 16.61/16.86  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 16.61/16.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.86  thf('10', plain,
% 16.61/16.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ 
% 16.61/16.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.61/16.86      inference('demod', [status(thm)], ['8', '9'])).
% 16.61/16.86  thf(t4_subset, axiom,
% 16.61/16.86    (![A:$i,B:$i,C:$i]:
% 16.61/16.86     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 16.61/16.86       ( m1_subset_1 @ A @ C ) ))).
% 16.61/16.86  thf('11', plain,
% 16.61/16.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 16.61/16.86         (~ (r2_hidden @ X8 @ X9)
% 16.61/16.86          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 16.61/16.86          | (m1_subset_1 @ X8 @ X10))),
% 16.61/16.86      inference('cnf', [status(esa)], [t4_subset])).
% 16.61/16.86  thf('12', plain,
% 16.61/16.86      (![X0 : $i]:
% 16.61/16.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86          | (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B))))),
% 16.61/16.86      inference('sup-', [status(thm)], ['10', '11'])).
% 16.61/16.86  thf('13', plain,
% 16.61/16.86      (![X0 : $i]:
% 16.61/16.86         ((r1_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.86          | (m1_subset_1 @ 
% 16.61/16.86             (sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ X0) @ 
% 16.61/16.86             (u1_struct_0 @ sk_A))
% 16.61/16.86          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.86      inference('sup-', [status(thm)], ['1', '12'])).
% 16.61/16.86  thf('14', plain,
% 16.61/16.86      (![X0 : $i, X1 : $i]:
% 16.61/16.86         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 16.61/16.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.86  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 16.61/16.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.86  thf(redefinition_k6_domain_1, axiom,
% 16.61/16.86    (![A:$i,B:$i]:
% 16.61/16.86     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 16.61/16.86       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 16.61/16.86  thf('16', plain,
% 16.61/16.86      (![X15 : $i, X16 : $i]:
% 16.61/16.86         ((v1_xboole_0 @ X15)
% 16.61/16.86          | ~ (m1_subset_1 @ X16 @ X15)
% 16.61/16.86          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 16.61/16.86      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 16.61/16.86  thf('17', plain,
% 16.61/16.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 16.61/16.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.86      inference('sup-', [status(thm)], ['15', '16'])).
% 16.61/16.86  thf(t55_tex_2, axiom,
% 16.61/16.86    (![A:$i]:
% 16.61/16.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 16.61/16.86         ( l1_pre_topc @ A ) ) =>
% 16.61/16.86       ( ![B:$i]:
% 16.61/16.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.61/16.86           ( ![C:$i]:
% 16.61/16.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 16.61/16.86               ( ( r2_hidden @
% 16.61/16.86                   B @ 
% 16.61/16.86                   ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 16.61/16.86                 ( ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 16.61/16.86                   ( k2_pre_topc @
% 16.61/16.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 16.61/16.86  thf('18', plain,
% 16.61/16.86      (![X17 : $i, X18 : $i, X19 : $i]:
% 16.61/16.86         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 16.61/16.86          | ~ (r2_hidden @ X17 @ 
% 16.61/16.86               (k2_pre_topc @ X18 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X19)))
% 16.61/16.86          | ((k2_pre_topc @ X18 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X17))
% 16.61/16.86              = (k2_pre_topc @ X18 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X19)))
% 16.61/16.86          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 16.61/16.86          | ~ (l1_pre_topc @ X18)
% 16.61/16.86          | ~ (v3_tdlat_3 @ X18)
% 16.61/16.86          | ~ (v2_pre_topc @ X18)
% 16.61/16.86          | (v2_struct_0 @ X18))),
% 16.61/16.86      inference('cnf', [status(esa)], [t55_tex_2])).
% 16.61/16.86  thf('19', plain,
% 16.61/16.86      (![X0 : $i]:
% 16.61/16.86         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.86          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.86          | (v2_struct_0 @ sk_A)
% 16.61/16.86          | ~ (v2_pre_topc @ sk_A)
% 16.61/16.86          | ~ (v3_tdlat_3 @ sk_A)
% 16.61/16.86          | ~ (l1_pre_topc @ sk_A)
% 16.61/16.86          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 16.61/16.86          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 16.61/16.86              = (k2_pre_topc @ sk_A @ 
% 16.61/16.86                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 16.61/16.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['17', '18'])).
% 16.61/16.87  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('21', plain, ((v3_tdlat_3 @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('23', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('24', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 16.61/16.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 16.61/16.87  thf('25', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87          | ~ (m1_subset_1 @ 
% 16.61/16.87               (sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ X0) @ 
% 16.61/16.87               (u1_struct_0 @ sk_A))
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ 
% 16.61/16.87              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 16.61/16.87               (sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ X0)))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['14', '24'])).
% 16.61/16.87  thf('26', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (r1_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ 
% 16.61/16.87              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 16.61/16.87               (sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ X0)))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 16.61/16.87          | (r1_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B))))),
% 16.61/16.87      inference('sup-', [status(thm)], ['13', '25'])).
% 16.61/16.87  thf('27', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         (((k2_pre_topc @ sk_A @ 
% 16.61/16.87            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 16.61/16.87             (sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ X0)))
% 16.61/16.87            = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | (r1_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('simplify', [status(thm)], ['26'])).
% 16.61/16.87  thf('28', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 16.61/16.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.87  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('30', plain,
% 16.61/16.87      (![X6 : $i, X7 : $i]:
% 16.61/16.87         ((r2_hidden @ X6 @ X7)
% 16.61/16.87          | (v1_xboole_0 @ X7)
% 16.61/16.87          | ~ (m1_subset_1 @ X6 @ X7))),
% 16.61/16.87      inference('cnf', [status(esa)], [t2_subset])).
% 16.61/16.87  thf('31', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['29', '30'])).
% 16.61/16.87  thf('32', plain,
% 16.61/16.87      (![X4 : $i, X5 : $i]:
% 16.61/16.87         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 16.61/16.87          | ~ (r2_hidden @ X4 @ X5))),
% 16.61/16.87      inference('cnf', [status(esa)], [t63_subset_1])).
% 16.61/16.87  thf('33', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 16.61/16.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.61/16.87      inference('sup-', [status(thm)], ['31', '32'])).
% 16.61/16.87  thf('34', plain,
% 16.61/16.87      (![X11 : $i, X12 : $i]:
% 16.61/16.87         (~ (l1_pre_topc @ X11)
% 16.61/16.87          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 16.61/16.87          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 16.61/16.87             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 16.61/16.87      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 16.61/16.87  thf('35', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.61/16.87        | ~ (l1_pre_topc @ sk_A))),
% 16.61/16.87      inference('sup-', [status(thm)], ['33', '34'])).
% 16.61/16.87  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('37', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.61/16.87      inference('demod', [status(thm)], ['35', '36'])).
% 16.61/16.87  thf('38', plain,
% 16.61/16.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 16.61/16.87         (~ (r2_hidden @ X8 @ X9)
% 16.61/16.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 16.61/16.87          | (m1_subset_1 @ X8 @ X10))),
% 16.61/16.87      inference('cnf', [status(esa)], [t4_subset])).
% 16.61/16.87  thf('39', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))))),
% 16.61/16.87      inference('sup-', [status(thm)], ['37', '38'])).
% 16.61/16.87  thf('40', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ X0)
% 16.61/16.87          | (m1_subset_1 @ 
% 16.61/16.87             (sk_C @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) @ 
% 16.61/16.87             (u1_struct_0 @ sk_A))
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['28', '39'])).
% 16.61/16.87  thf('41', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 16.61/16.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.87  thf('42', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('43', plain,
% 16.61/16.87      (![X15 : $i, X16 : $i]:
% 16.61/16.87         ((v1_xboole_0 @ X15)
% 16.61/16.87          | ~ (m1_subset_1 @ X16 @ X15)
% 16.61/16.87          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 16.61/16.87      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 16.61/16.87  thf('44', plain,
% 16.61/16.87      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['42', '43'])).
% 16.61/16.87  thf('45', plain,
% 16.61/16.87      (![X17 : $i, X18 : $i, X19 : $i]:
% 16.61/16.87         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 16.61/16.87          | ~ (r2_hidden @ X17 @ 
% 16.61/16.87               (k2_pre_topc @ X18 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X19)))
% 16.61/16.87          | ((k2_pre_topc @ X18 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X17))
% 16.61/16.87              = (k2_pre_topc @ X18 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X19)))
% 16.61/16.87          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 16.61/16.87          | ~ (l1_pre_topc @ X18)
% 16.61/16.87          | ~ (v3_tdlat_3 @ X18)
% 16.61/16.87          | ~ (v2_pre_topc @ X18)
% 16.61/16.87          | (v2_struct_0 @ X18))),
% 16.61/16.87      inference('cnf', [status(esa)], [t55_tex_2])).
% 16.61/16.87  thf('46', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | ~ (v2_pre_topc @ sk_A)
% 16.61/16.87          | ~ (v3_tdlat_3 @ sk_A)
% 16.61/16.87          | ~ (l1_pre_topc @ sk_A)
% 16.61/16.87          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['44', '45'])).
% 16.61/16.87  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('48', plain, ((v3_tdlat_3 @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('50', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('51', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 16.61/16.87  thf('52', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ X0)
% 16.61/16.87          | ~ (m1_subset_1 @ 
% 16.61/16.87               (sk_C @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) @ 
% 16.61/16.87               (u1_struct_0 @ sk_A))
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ 
% 16.61/16.87              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 16.61/16.87               (sk_C @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['41', '51'])).
% 16.61/16.87  thf('53', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ X0)
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | ((k2_pre_topc @ sk_A @ 
% 16.61/16.87              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 16.61/16.87               (sk_C @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))))
% 16.61/16.87              = (k2_pre_topc @ sk_A @ 
% 16.61/16.87                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ X0))),
% 16.61/16.87      inference('sup-', [status(thm)], ['40', '52'])).
% 16.61/16.87  thf('54', plain,
% 16.61/16.87      (![X0 : $i]:
% 16.61/16.87         (((k2_pre_topc @ sk_A @ 
% 16.61/16.87            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 16.61/16.87             (sk_C @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))))
% 16.61/16.87            = (k2_pre_topc @ sk_A @ 
% 16.61/16.87               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87          | (v2_struct_0 @ sk_A)
% 16.61/16.87          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ X0)
% 16.61/16.87          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('simplify', [status(thm)], ['53'])).
% 16.61/16.87  thf('55', plain,
% 16.61/16.87      ((((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 16.61/16.87          = (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87        | (v2_struct_0 @ sk_A)
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87        | (v2_struct_0 @ sk_A))),
% 16.61/16.87      inference('sup+', [status(thm)], ['27', '54'])).
% 16.61/16.87  thf('56', plain,
% 16.61/16.87      (((v2_struct_0 @ sk_A)
% 16.61/16.87        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 16.61/16.87            = (k2_pre_topc @ sk_A @ 
% 16.61/16.87               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 16.61/16.87      inference('simplify', [status(thm)], ['55'])).
% 16.61/16.87  thf('57', plain,
% 16.61/16.87      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 16.61/16.87         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('58', plain,
% 16.61/16.87      (((v2_struct_0 @ sk_A)
% 16.61/16.87        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 16.61/16.87  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('60', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B))))),
% 16.61/16.87      inference('clc', [status(thm)], ['58', '59'])).
% 16.61/16.87  thf('61', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 16.61/16.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.87  thf('62', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 16.61/16.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.87  thf('63', plain,
% 16.61/16.87      (![X0 : $i, X2 : $i, X3 : $i]:
% 16.61/16.87         (~ (r2_hidden @ X2 @ X0)
% 16.61/16.87          | ~ (r2_hidden @ X2 @ X3)
% 16.61/16.87          | ~ (r1_xboole_0 @ X0 @ X3))),
% 16.61/16.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 16.61/16.87  thf('64', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X1 @ X0)
% 16.61/16.87          | ~ (r1_xboole_0 @ X0 @ X2)
% 16.61/16.87          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 16.61/16.87      inference('sup-', [status(thm)], ['62', '63'])).
% 16.61/16.87  thf('65', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i]:
% 16.61/16.87         ((r1_xboole_0 @ X0 @ X1)
% 16.61/16.87          | ~ (r1_xboole_0 @ X1 @ X0)
% 16.61/16.87          | (r1_xboole_0 @ X0 @ X1))),
% 16.61/16.87      inference('sup-', [status(thm)], ['61', '64'])).
% 16.61/16.87  thf('66', plain,
% 16.61/16.87      (![X0 : $i, X1 : $i]:
% 16.61/16.87         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 16.61/16.87      inference('simplify', [status(thm)], ['65'])).
% 16.61/16.87  thf('67', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))))),
% 16.61/16.87      inference('sup-', [status(thm)], ['60', '66'])).
% 16.61/16.87  thf('68', plain,
% 16.61/16.87      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['42', '43'])).
% 16.61/16.87  thf('69', plain,
% 16.61/16.87      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['15', '16'])).
% 16.61/16.87  thf('70', plain,
% 16.61/16.87      (~ (r1_xboole_0 @ 
% 16.61/16.87          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 16.61/16.87          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf('71', plain,
% 16.61/16.87      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['69', '70'])).
% 16.61/16.87  thf('72', plain,
% 16.61/16.87      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ 
% 16.61/16.87           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 16.61/16.87      inference('sup-', [status(thm)], ['68', '71'])).
% 16.61/16.87  thf('73', plain,
% 16.61/16.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 16.61/16.87        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B)) @ 
% 16.61/16.87             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))))),
% 16.61/16.87      inference('simplify', [status(thm)], ['72'])).
% 16.61/16.87  thf('74', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 16.61/16.87      inference('clc', [status(thm)], ['67', '73'])).
% 16.61/16.87  thf(fc2_struct_0, axiom,
% 16.61/16.87    (![A:$i]:
% 16.61/16.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 16.61/16.87       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 16.61/16.87  thf('75', plain,
% 16.61/16.87      (![X14 : $i]:
% 16.61/16.87         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 16.61/16.87          | ~ (l1_struct_0 @ X14)
% 16.61/16.87          | (v2_struct_0 @ X14))),
% 16.61/16.87      inference('cnf', [status(esa)], [fc2_struct_0])).
% 16.61/16.87  thf('76', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 16.61/16.87      inference('sup-', [status(thm)], ['74', '75'])).
% 16.61/16.87  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 16.61/16.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.61/16.87  thf(dt_l1_pre_topc, axiom,
% 16.61/16.87    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 16.61/16.87  thf('78', plain,
% 16.61/16.87      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 16.61/16.87      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 16.61/16.87  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 16.61/16.87      inference('sup-', [status(thm)], ['77', '78'])).
% 16.61/16.87  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 16.61/16.87      inference('demod', [status(thm)], ['76', '79'])).
% 16.61/16.87  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 16.61/16.87  
% 16.61/16.87  % SZS output end Refutation
% 16.61/16.87  
% 16.61/16.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
