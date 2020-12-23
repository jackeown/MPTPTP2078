%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N38EVrjlCL

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  221 (4410 expanded)
%              Number of leaves         :   40 (1336 expanded)
%              Depth                    :   41
%              Number of atoms          : 1483 (41011 expanded)
%              Number of equality atoms :   37 ( 518 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t44_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ~ ( v2_struct_0 @ ( sk_C @ X28 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('43',plain,(
    r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('50',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
    = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','53'])).

thf('55',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('57',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('61',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','64'])).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ X0 )
        | ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ X0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('72',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','64'])).

thf('74',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('78',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('80',plain,
    ( ( ( ( k6_domain_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( sk_B_1
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','82'])).

thf('84',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,
    ( ( ( sk_B_1
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['87','96'])).

thf('98',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('99',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('101',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','99','100'])).

thf('102',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( m1_pre_topc @ ( sk_C @ X28 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','101'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['117','118'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(cc2_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('124',plain,(
    ! [X23: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_tdlat_3 @ X23 )
      | ( v7_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('125',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( v1_tdlat_3 @ ( sk_C @ X28 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','99','100'])).

thf('139',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','139'])).

thf('141',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['117','118'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('142',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_tdlat_3 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('151',plain,(
    ! [X21: $i] :
      ( ~ ( v1_tdlat_3 @ X21 )
      | ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('152',plain,
    ( ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('154',plain,(
    v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','149','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( X28
        = ( u1_struct_0 @ ( sk_C @ X28 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','101'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('168',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('169',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('171',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','99'])).

thf('172',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['169','172'])).

thf('174',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('175',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('176',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('178',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['155','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['107','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N38EVrjlCL
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 285 iterations in 0.159s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.61  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.37/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.61  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.37/0.61  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.37/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.61  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(t44_tex_2, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.37/0.61         ( l1_pre_topc @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.61           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.61            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.61              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t34_tex_2, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.61           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.37/0.61                ( ![C:$i]:
% 0.37/0.61                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.37/0.61                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.61                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X28)
% 0.37/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.61          | ~ (v2_tex_2 @ X28 @ X29)
% 0.37/0.61          | ~ (v2_struct_0 @ (sk_C @ X28 @ X29))
% 0.37/0.61          | ~ (l1_pre_topc @ X29)
% 0.37/0.61          | ~ (v2_pre_topc @ X29)
% 0.37/0.61          | (v2_struct_0 @ X29))),
% 0.37/0.61      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.61  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.37/0.61  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['6'])).
% 0.37/0.61  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('split', [status(esa)], ['8'])).
% 0.37/0.61  thf(d1_xboole_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.61  thf(t1_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf(redefinition_k6_domain_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.61       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X19)
% 0.37/0.61          | ~ (m1_subset_1 @ X20 @ X19)
% 0.37/0.61          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0)
% 0.37/0.61          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.37/0.61          | (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.37/0.61          | (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.61  thf(l1_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X7 : $i, X9 : $i]:
% 0.37/0.61         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf(t1_tex_2, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.37/0.61           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X26)
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X26)
% 0.37/0.61          | ((X27) = (X26))
% 0.37/0.61          | ~ (r1_tarski @ X27 @ X26)
% 0.37/0.61          | (v1_xboole_0 @ X27))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.37/0.61          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_zfmisc_1 @ X0)
% 0.37/0.61          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.61          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.37/0.61          | (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.61  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.37/0.61  thf('22', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0)
% 0.37/0.61          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (X0))
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['15', '23'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_zfmisc_1 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (X0)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf('27', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('split', [status(esa)], ['6'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0)
% 0.37/0.61          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i]:
% 0.37/0.61         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('31', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf(t1_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.61       ( r1_tarski @ A @ C ) ))).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X3 @ X4)
% 0.37/0.61          | ~ (r1_tarski @ X4 @ X5)
% 0.37/0.61          | (r1_tarski @ X3 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0)
% 0.37/0.61          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.37/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['31', '34'])).
% 0.37/0.61  thf('36', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X0)
% 0.37/0.61          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.37/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (((r1_tarski @ (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))) @ 
% 0.37/0.61         (u1_struct_0 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf('40', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      ((r1_tarski @ (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))) @ 
% 0.37/0.61        (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['39', '40'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      ((r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.37/0.61        (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      ((m1_subset_1 @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.37/0.61        (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X19)
% 0.37/0.61          | ~ (m1_subset_1 @ X20 @ X19)
% 0.37/0.61          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61          (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.61          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.61  thf('50', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.61  thf('52', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61         (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.61         = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))),
% 0.37/0.61      inference('clc', [status(thm)], ['47', '52'])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.61          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.61        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['28', '53'])).
% 0.37/0.61  thf('55', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.61  thf('57', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X19)
% 0.37/0.61          | ~ (m1_subset_1 @ X20 @ X19)
% 0.37/0.61          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.61  thf('59', plain,
% 0.37/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.61          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.61  thf('60', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.61  thf('61', plain,
% 0.37/0.61      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.61         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.37/0.61      inference('clc', [status(thm)], ['59', '60'])).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.61          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.37/0.61        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['54', '61'])).
% 0.37/0.61  thf('63', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      ((~ (v1_zfmisc_1 @ sk_B_1)
% 0.37/0.61        | ((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.61            = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))),
% 0.37/0.61      inference('clc', [status(thm)], ['62', '63'])).
% 0.37/0.61  thf('65', plain,
% 0.37/0.61      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.61          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '64'])).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      ((![X0 : $i]:
% 0.37/0.61          (~ (r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ X0)
% 0.37/0.61           | (r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ X0)))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.61  thf('68', plain,
% 0.37/0.61      ((((v1_xboole_0 @ sk_B_1)
% 0.37/0.61         | (r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ sk_B_1)))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['26', '67'])).
% 0.37/0.61  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      (((r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ sk_B_1))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('clc', [status(thm)], ['68', '69'])).
% 0.37/0.61  thf('71', plain,
% 0.37/0.61      (![X7 : $i, X9 : $i]:
% 0.37/0.61         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.61  thf('72', plain,
% 0.37/0.61      (((r1_tarski @ (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))) @ 
% 0.37/0.61         sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.37/0.61  thf('73', plain,
% 0.37/0.61      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.37/0.61          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '64'])).
% 0.37/0.61  thf('74', plain,
% 0.37/0.61      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.37/0.61  thf('75', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.61  thf('76', plain,
% 0.37/0.61      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['74', '75'])).
% 0.37/0.61  thf('77', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.61  thf('78', plain,
% 0.37/0.61      (((m1_subset_1 @ (sk_B @ sk_B_1) @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.61  thf('79', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X19)
% 0.37/0.61          | ~ (m1_subset_1 @ X20 @ X19)
% 0.37/0.61          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.61  thf('80', plain,
% 0.37/0.61      (((((k6_domain_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.37/0.61           = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.61         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['78', '79'])).
% 0.37/0.61  thf('81', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('82', plain,
% 0.37/0.61      ((((k6_domain_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.37/0.61          = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('clc', [status(thm)], ['80', '81'])).
% 0.37/0.61  thf('83', plain,
% 0.37/0.61      (((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.37/0.61         | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61         | ~ (v1_zfmisc_1 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['25', '82'])).
% 0.37/0.61  thf('84', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('split', [status(esa)], ['6'])).
% 0.37/0.61  thf('85', plain,
% 0.37/0.61      (((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))) | (v1_xboole_0 @ sk_B_1)))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.61  thf('86', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('87', plain,
% 0.37/0.61      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.37/0.61         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('clc', [status(thm)], ['85', '86'])).
% 0.37/0.61  thf('88', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.61  thf(t36_tex_2, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.61           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.37/0.61  thf('89', plain,
% 0.37/0.61      (![X30 : $i, X31 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.37/0.61          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.37/0.61          | ~ (l1_pre_topc @ X31)
% 0.37/0.61          | ~ (v2_pre_topc @ X31)
% 0.37/0.61          | (v2_struct_0 @ X31))),
% 0.37/0.61      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.37/0.61  thf('90', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.37/0.61           sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.61  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('93', plain,
% 0.37/0.61      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.37/0.61         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.37/0.61      inference('clc', [status(thm)], ['59', '60'])).
% 0.37/0.61  thf('94', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.37/0.61  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('96', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.37/0.61      inference('clc', [status(thm)], ['94', '95'])).
% 0.37/0.61  thf('97', plain,
% 0.37/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['87', '96'])).
% 0.37/0.61  thf('98', plain,
% 0.37/0.61      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['8'])).
% 0.37/0.61  thf('99', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.61  thf('100', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.37/0.61      inference('split', [status(esa)], ['6'])).
% 0.37/0.61  thf('101', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['9', '99', '100'])).
% 0.37/0.61  thf('102', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['7', '101'])).
% 0.37/0.61  thf('103', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['5', '102'])).
% 0.37/0.61  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('105', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['103', '104'])).
% 0.37/0.61  thf('106', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('107', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['105', '106'])).
% 0.37/0.61  thf('108', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('109', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X28)
% 0.37/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.61          | ~ (v2_tex_2 @ X28 @ X29)
% 0.37/0.61          | (m1_pre_topc @ (sk_C @ X28 @ X29) @ X29)
% 0.37/0.61          | ~ (l1_pre_topc @ X29)
% 0.37/0.61          | ~ (v2_pre_topc @ X29)
% 0.37/0.61          | (v2_struct_0 @ X29))),
% 0.37/0.61      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.61  thf('110', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['108', '109'])).
% 0.37/0.61  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('113', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.37/0.61  thf('114', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['7', '101'])).
% 0.37/0.61  thf('115', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['113', '114'])).
% 0.37/0.61  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('117', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['115', '116'])).
% 0.37/0.61  thf('118', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('119', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.61      inference('clc', [status(thm)], ['117', '118'])).
% 0.37/0.61  thf(dt_m1_pre_topc, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.61  thf('120', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i]:
% 0.37/0.61         (~ (m1_pre_topc @ X16 @ X17)
% 0.37/0.61          | (l1_pre_topc @ X16)
% 0.37/0.61          | ~ (l1_pre_topc @ X17))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.61  thf('121', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['119', '120'])).
% 0.37/0.61  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('123', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['121', '122'])).
% 0.37/0.61  thf(cc2_tex_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.61           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.37/0.61         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.37/0.61  thf('124', plain,
% 0.37/0.61      (![X23 : $i]:
% 0.37/0.61         ((v2_struct_0 @ X23)
% 0.37/0.61          | ~ (v2_pre_topc @ X23)
% 0.37/0.61          | ~ (v1_tdlat_3 @ X23)
% 0.37/0.61          | ~ (v2_tdlat_3 @ X23)
% 0.37/0.61          | (v7_struct_0 @ X23)
% 0.37/0.61          | ~ (l1_pre_topc @ X23))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.37/0.61  thf('125', plain,
% 0.37/0.61      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['123', '124'])).
% 0.37/0.61  thf('126', plain,
% 0.37/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['6'])).
% 0.37/0.61  thf('127', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('128', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X28)
% 0.37/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.61          | ~ (v2_tex_2 @ X28 @ X29)
% 0.37/0.61          | (v1_tdlat_3 @ (sk_C @ X28 @ X29))
% 0.37/0.61          | ~ (l1_pre_topc @ X29)
% 0.37/0.61          | ~ (v2_pre_topc @ X29)
% 0.37/0.61          | (v2_struct_0 @ X29))),
% 0.37/0.61      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.61  thf('129', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['127', '128'])).
% 0.37/0.61  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('132', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.37/0.61  thf('133', plain,
% 0.37/0.61      ((((v1_xboole_0 @ sk_B_1)
% 0.37/0.61         | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['126', '132'])).
% 0.37/0.61  thf('134', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('135', plain,
% 0.37/0.61      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.37/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['133', '134'])).
% 0.37/0.61  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('137', plain,
% 0.37/0.61      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.61         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['135', '136'])).
% 0.37/0.61  thf('138', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['9', '99', '100'])).
% 0.37/0.61  thf('139', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 0.37/0.61  thf('140', plain,
% 0.37/0.61      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['125', '139'])).
% 0.37/0.61  thf('141', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.61      inference('clc', [status(thm)], ['117', '118'])).
% 0.37/0.61  thf(cc6_tdlat_3, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.37/0.61         ( l1_pre_topc @ A ) ) =>
% 0.37/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.37/0.61  thf('142', plain,
% 0.37/0.61      (![X24 : $i, X25 : $i]:
% 0.37/0.61         (~ (m1_pre_topc @ X24 @ X25)
% 0.37/0.61          | (v2_tdlat_3 @ X24)
% 0.37/0.61          | ~ (l1_pre_topc @ X25)
% 0.37/0.61          | ~ (v2_tdlat_3 @ X25)
% 0.37/0.61          | ~ (v2_pre_topc @ X25)
% 0.37/0.61          | (v2_struct_0 @ X25))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.37/0.61  thf('143', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61        | ~ (v2_tdlat_3 @ sk_A)
% 0.37/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['141', '142'])).
% 0.37/0.61  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('145', plain, ((v2_tdlat_3 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('147', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.37/0.61  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('149', plain, ((v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['147', '148'])).
% 0.37/0.61  thf('150', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['121', '122'])).
% 0.37/0.61  thf(cc1_tdlat_3, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.37/0.61  thf('151', plain,
% 0.37/0.61      (![X21 : $i]:
% 0.37/0.61         (~ (v1_tdlat_3 @ X21) | (v2_pre_topc @ X21) | ~ (l1_pre_topc @ X21))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.37/0.61  thf('152', plain,
% 0.37/0.61      (((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['150', '151'])).
% 0.37/0.61  thf('153', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 0.37/0.61  thf('154', plain, ((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['152', '153'])).
% 0.37/0.61  thf('155', plain,
% 0.37/0.61      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['140', '149', '154'])).
% 0.37/0.61  thf('156', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('157', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X28)
% 0.37/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.61          | ~ (v2_tex_2 @ X28 @ X29)
% 0.37/0.61          | ((X28) = (u1_struct_0 @ (sk_C @ X28 @ X29)))
% 0.37/0.61          | ~ (l1_pre_topc @ X29)
% 0.37/0.61          | ~ (v2_pre_topc @ X29)
% 0.37/0.61          | (v2_struct_0 @ X29))),
% 0.37/0.61      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.37/0.61  thf('158', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['156', '157'])).
% 0.37/0.61  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('161', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.61        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.37/0.61  thf('162', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['7', '101'])).
% 0.37/0.61  thf('163', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['161', '162'])).
% 0.37/0.61  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('165', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.37/0.61      inference('clc', [status(thm)], ['163', '164'])).
% 0.37/0.61  thf('166', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('167', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['165', '166'])).
% 0.37/0.61  thf(fc7_struct_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.61       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.37/0.61  thf('168', plain,
% 0.37/0.61      (![X18 : $i]:
% 0.37/0.61         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.37/0.61          | ~ (l1_struct_0 @ X18)
% 0.37/0.61          | ~ (v7_struct_0 @ X18))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.37/0.61  thf('169', plain,
% 0.37/0.61      (((v1_zfmisc_1 @ sk_B_1)
% 0.37/0.61        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['167', '168'])).
% 0.37/0.61  thf('170', plain,
% 0.37/0.61      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.37/0.61      inference('split', [status(esa)], ['8'])).
% 0.37/0.61  thf('171', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['9', '99'])).
% 0.37/0.61  thf('172', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.37/0.61      inference('simpl_trail', [status(thm)], ['170', '171'])).
% 0.37/0.61  thf('173', plain,
% 0.37/0.61      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.61        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['169', '172'])).
% 0.37/0.61  thf('174', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['121', '122'])).
% 0.37/0.61  thf(dt_l1_pre_topc, axiom,
% 0.37/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.61  thf('175', plain,
% 0.37/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('176', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['174', '175'])).
% 0.37/0.61  thf('177', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['173', '176'])).
% 0.37/0.61  thf('178', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['155', '177'])).
% 0.37/0.61  thf('179', plain, ($false), inference('demod', [status(thm)], ['107', '178'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
