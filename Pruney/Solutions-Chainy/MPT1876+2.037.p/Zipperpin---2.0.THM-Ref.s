%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jMpRIYhaZw

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:01 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 653 expanded)
%              Number of leaves         :   41 ( 199 expanded)
%              Depth                    :   25
%              Number of atoms          : 1205 (7284 expanded)
%              Number of equality atoms :   29 (  78 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( X28 = X27 )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( X25
        = ( u1_struct_0 @ ( sk_C_1 @ X25 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('33',plain,
    ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
    = ( u1_struct_0 @ ( sk_C_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( X25
        = ( u1_struct_0 @ ( sk_C_1 @ X25 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('50',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('57',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['47','64'])).

thf('66',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','67'])).

thf('69',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','68'])).

thf('70',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('72',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X25 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('86',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','87'])).

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

thf('89',plain,(
    ! [X22: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v1_tdlat_3 @ X22 )
      | ~ ( v2_tdlat_3 @ X22 )
      | ( v7_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X25 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('101',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('103',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('112',plain,(
    ! [X21: $i] :
      ( ~ ( v2_tdlat_3 @ X21 )
      | ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('113',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('115',plain,(
    v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','110','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

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

thf('119',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( X31
       != ( u1_struct_0 @ X29 ) )
      | ~ ( v2_tex_2 @ X31 @ X30 )
      | ( v1_tdlat_3 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('120',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_tdlat_3 @ X29 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X29 ) @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B_1 @ X0 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('127',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('128',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','67','127'])).

thf('129',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['126','128'])).

thf('130',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('135',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['116','135'])).

thf('137',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['88','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['69','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jMpRIYhaZw
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 518 iterations in 0.356s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.80  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.80  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.58/0.80  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.58/0.80  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.58/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.80  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.58/0.80  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.58/0.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.80  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(t44_tex_2, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.58/0.80         ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.58/0.80             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.80           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.58/0.80                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.80              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.58/0.80  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('3', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('4', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.80      inference('split', [status(esa)], ['3'])).
% 0.58/0.80  thf(d1_xboole_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf(t63_subset_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( r2_hidden @ A @ B ) =>
% 0.58/0.80       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.58/0.80          | ~ (r2_hidden @ X8 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X0)
% 0.58/0.80          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.80  thf(t3_subset, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i]:
% 0.58/0.80         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.80  thf(t1_tex_2, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.58/0.80           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (![X27 : $i, X28 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X27)
% 0.58/0.80          | ~ (v1_zfmisc_1 @ X27)
% 0.58/0.80          | ((X28) = (X27))
% 0.58/0.80          | ~ (r1_tarski @ X28 @ X27)
% 0.58/0.80          | (v1_xboole_0 @ X28))),
% 0.58/0.80      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X0)
% 0.58/0.80          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.58/0.80          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.58/0.80          | ~ (v1_zfmisc_1 @ X0)
% 0.58/0.80          | (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v1_zfmisc_1 @ X0)
% 0.58/0.80          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.58/0.80          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.58/0.80          | (v1_xboole_0 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.80  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.58/0.80  thf('13', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X0)
% 0.58/0.80          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.58/0.80          | ~ (v1_zfmisc_1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i]:
% 0.58/0.80         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.80  thf('18', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf(d3_tarski, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X3 @ X4)
% 0.58/0.80          | (r2_hidden @ X3 @ X5)
% 0.58/0.80          | ~ (r1_tarski @ X4 @ X5))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.80        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['15', '20'])).
% 0.58/0.80  thf('22', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('23', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.58/0.80          | ~ (r2_hidden @ X8 @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      ((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.58/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf(t10_tsep_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.58/0.80             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.80           ( ?[C:$i]:
% 0.58/0.80             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.58/0.80               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (![X25 : $i, X26 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X25)
% 0.58/0.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.58/0.80          | ((X25) = (u1_struct_0 @ (sk_C_1 @ X25 @ X26)))
% 0.58/0.80          | ~ (l1_pre_topc @ X26)
% 0.58/0.80          | (v2_struct_0 @ X26))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | ((k1_tarski @ (sk_B @ sk_B_1))
% 0.58/0.80            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.58/0.80        | (v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.80  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ((k1_tarski @ (sk_B @ sk_B_1))
% 0.58/0.80            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.58/0.80        | (v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.58/0.80      inference('demod', [status(thm)], ['27', '28'])).
% 0.58/0.80  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.58/0.80        | ((k1_tarski @ (sk_B @ sk_B_1))
% 0.58/0.80            = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))))),
% 0.58/0.80      inference('clc', [status(thm)], ['29', '30'])).
% 0.58/0.80  thf('32', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (((k1_tarski @ (sk_B @ sk_B_1))
% 0.58/0.80         = (u1_struct_0 @ (sk_C_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['31', '32'])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.58/0.80          = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.58/0.80        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['14', '33'])).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (![X25 : $i, X26 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X25)
% 0.58/0.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.58/0.80          | ((X25) = (u1_struct_0 @ (sk_C_1 @ X25 @ X26)))
% 0.58/0.80          | ~ (l1_pre_topc @ X26)
% 0.58/0.80          | (v2_struct_0 @ X26))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.80  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.80  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('41', plain,
% 0.58/0.80      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.80        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.58/0.80      inference('clc', [status(thm)], ['39', '40'])).
% 0.58/0.80  thf('42', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('43', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.58/0.80        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['34', '43'])).
% 0.58/0.80  thf('45', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      ((~ (v1_zfmisc_1 @ sk_B_1) | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))),
% 0.58/0.80      inference('clc', [status(thm)], ['44', '45'])).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.58/0.80         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['4', '46'])).
% 0.58/0.80  thf('48', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf(t1_subset, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X10 : $i, X11 : $i]:
% 0.58/0.80         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.58/0.80      inference('cnf', [status(esa)], [t1_subset])).
% 0.58/0.80  thf('50', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf(t36_tex_2, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X32 : $i, X33 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 0.58/0.80          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X33) @ X32) @ X33)
% 0.58/0.80          | ~ (l1_pre_topc @ X33)
% 0.58/0.80          | ~ (v2_pre_topc @ X33)
% 0.58/0.80          | (v2_struct_0 @ X33))),
% 0.58/0.80      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.58/0.80           sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.80  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('55', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf(redefinition_k6_domain_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.58/0.80       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      (![X19 : $i, X20 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X19)
% 0.58/0.80          | ~ (m1_subset_1 @ X20 @ X19)
% 0.58/0.80          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.58/0.80          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.58/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['55', '56'])).
% 0.58/0.80  thf('58', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('59', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.80  thf('60', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('61', plain,
% 0.58/0.80      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.58/0.80         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.58/0.80      inference('clc', [status(thm)], ['57', '60'])).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['52', '53', '54', '61'])).
% 0.58/0.80  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('64', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['62', '63'])).
% 0.58/0.80  thf('65', plain,
% 0.58/0.80      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['47', '64'])).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('67', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.80  thf('68', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['2', '67'])).
% 0.58/0.80  thf('69', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['1', '68'])).
% 0.58/0.80  thf('70', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf(fc7_struct_0, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.80       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      (![X18 : $i]:
% 0.58/0.80         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.58/0.80          | ~ (l1_struct_0 @ X18)
% 0.58/0.80          | ~ (v7_struct_0 @ X18))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (((v1_zfmisc_1 @ sk_B_1)
% 0.58/0.80        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('74', plain,
% 0.58/0.80      (![X25 : $i, X26 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X25)
% 0.58/0.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.58/0.80          | (m1_pre_topc @ (sk_C_1 @ X25 @ X26) @ X26)
% 0.58/0.80          | ~ (l1_pre_topc @ X26)
% 0.58/0.80          | (v2_struct_0 @ X26))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.58/0.80  thf('75', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.80  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['75', '76'])).
% 0.58/0.80  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('79', plain,
% 0.58/0.80      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.80        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['77', '78'])).
% 0.58/0.80  thf('80', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('81', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['79', '80'])).
% 0.58/0.80  thf(dt_m1_pre_topc, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) =>
% 0.58/0.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X16 @ X17)
% 0.58/0.80          | (l1_pre_topc @ X16)
% 0.58/0.80          | ~ (l1_pre_topc @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.80  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('85', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['83', '84'])).
% 0.58/0.80  thf(dt_l1_pre_topc, axiom,
% 0.58/0.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.80  thf('87', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['85', '86'])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['72', '87'])).
% 0.58/0.80  thf(cc2_tex_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) =>
% 0.58/0.80       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.58/0.80         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      (![X22 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X22)
% 0.58/0.80          | ~ (v2_pre_topc @ X22)
% 0.58/0.80          | ~ (v1_tdlat_3 @ X22)
% 0.58/0.80          | ~ (v2_tdlat_3 @ X22)
% 0.58/0.80          | (v7_struct_0 @ X22)
% 0.58/0.80          | ~ (l1_pre_topc @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.58/0.80  thf('90', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('91', plain,
% 0.58/0.80      (![X25 : $i, X26 : $i]:
% 0.58/0.80         ((v1_xboole_0 @ X25)
% 0.58/0.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.58/0.80          | ~ (v2_struct_0 @ (sk_C_1 @ X25 @ X26))
% 0.58/0.80          | ~ (l1_pre_topc @ X26)
% 0.58/0.80          | (v2_struct_0 @ X26))),
% 0.58/0.80      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.58/0.80  thf('92', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['90', '91'])).
% 0.58/0.80  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('94', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['92', '93'])).
% 0.58/0.80  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('96', plain,
% 0.58/0.80      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['94', '95'])).
% 0.58/0.80  thf('97', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('98', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['96', '97'])).
% 0.58/0.80  thf('99', plain,
% 0.58/0.80      ((~ (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['89', '98'])).
% 0.58/0.80  thf('100', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['83', '84'])).
% 0.58/0.80  thf('101', plain,
% 0.58/0.80      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['99', '100'])).
% 0.58/0.80  thf('102', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['79', '80'])).
% 0.58/0.80  thf(cc6_tdlat_3, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.58/0.80         ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.58/0.80  thf('103', plain,
% 0.58/0.80      (![X23 : $i, X24 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X23 @ X24)
% 0.58/0.80          | (v2_tdlat_3 @ X23)
% 0.58/0.80          | ~ (l1_pre_topc @ X24)
% 0.58/0.80          | ~ (v2_tdlat_3 @ X24)
% 0.58/0.80          | ~ (v2_pre_topc @ X24)
% 0.58/0.80          | (v2_struct_0 @ X24))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.58/0.80  thf('104', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80        | ~ (v2_tdlat_3 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['102', '103'])).
% 0.58/0.80  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('106', plain, ((v2_tdlat_3 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('108', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.58/0.80  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('110', plain, ((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['108', '109'])).
% 0.58/0.80  thf('111', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['83', '84'])).
% 0.58/0.80  thf(cc2_tdlat_3, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.58/0.80  thf('112', plain,
% 0.58/0.80      (![X21 : $i]:
% 0.58/0.80         (~ (v2_tdlat_3 @ X21) | (v2_pre_topc @ X21) | ~ (l1_pre_topc @ X21))),
% 0.58/0.80      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.58/0.80  thf('113', plain,
% 0.58/0.80      (((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['111', '112'])).
% 0.58/0.80  thf('114', plain, ((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['108', '109'])).
% 0.58/0.80  thf('115', plain, ((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['113', '114'])).
% 0.58/0.80  thf('116', plain,
% 0.58/0.80      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['101', '110', '115'])).
% 0.58/0.80  thf('117', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('118', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf(t26_tex_2, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.58/0.80                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('119', plain,
% 0.58/0.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X29)
% 0.58/0.80          | ~ (m1_pre_topc @ X29 @ X30)
% 0.58/0.80          | ((X31) != (u1_struct_0 @ X29))
% 0.58/0.80          | ~ (v2_tex_2 @ X31 @ X30)
% 0.58/0.80          | (v1_tdlat_3 @ X29)
% 0.58/0.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.58/0.80          | ~ (l1_pre_topc @ X30)
% 0.58/0.80          | (v2_struct_0 @ X30))),
% 0.58/0.80      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.58/0.80  thf('120', plain,
% 0.58/0.80      (![X29 : $i, X30 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X30)
% 0.58/0.80          | ~ (l1_pre_topc @ X30)
% 0.58/0.80          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.58/0.80               (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.58/0.80          | (v1_tdlat_3 @ X29)
% 0.58/0.80          | ~ (v2_tex_2 @ (u1_struct_0 @ X29) @ X30)
% 0.58/0.80          | ~ (m1_pre_topc @ X29 @ X30)
% 0.58/0.80          | (v2_struct_0 @ X29))),
% 0.58/0.80      inference('simplify', [status(thm)], ['119'])).
% 0.58/0.80  thf('121', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.58/0.80          | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80          | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0)
% 0.58/0.80          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)) @ X0)
% 0.58/0.80          | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80          | ~ (l1_pre_topc @ X0)
% 0.58/0.80          | (v2_struct_0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['118', '120'])).
% 0.58/0.80  thf('122', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf('123', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.58/0.80          | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80          | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0)
% 0.58/0.80          | ~ (v2_tex_2 @ sk_B_1 @ X0)
% 0.58/0.80          | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80          | ~ (l1_pre_topc @ X0)
% 0.58/0.80          | (v2_struct_0 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['121', '122'])).
% 0.58/0.80  thf('124', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.80        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['117', '123'])).
% 0.58/0.80  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('126', plain,
% 0.58/0.80      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('split', [status(esa)], ['3'])).
% 0.58/0.80  thf('127', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.58/0.80      inference('split', [status(esa)], ['3'])).
% 0.58/0.80  thf('128', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['2', '67', '127'])).
% 0.58/0.80  thf('129', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['126', '128'])).
% 0.58/0.80  thf('130', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['79', '80'])).
% 0.58/0.80  thf('131', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['124', '125', '129', '130'])).
% 0.58/0.80  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('133', plain,
% 0.58/0.80      (((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.58/0.80        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['131', '132'])).
% 0.58/0.80  thf('134', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['96', '97'])).
% 0.58/0.80  thf('135', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('clc', [status(thm)], ['133', '134'])).
% 0.58/0.80  thf('136', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['116', '135'])).
% 0.58/0.80  thf('137', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.58/0.80      inference('demod', [status(thm)], ['88', '136'])).
% 0.58/0.80  thf('138', plain, ($false), inference('demod', [status(thm)], ['69', '137'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
