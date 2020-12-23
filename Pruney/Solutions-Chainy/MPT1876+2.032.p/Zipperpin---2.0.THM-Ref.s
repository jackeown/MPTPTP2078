%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H8CZ8312HP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  182 (1314 expanded)
%              Number of leaves         :   41 ( 392 expanded)
%              Depth                    :   27
%              Number of atoms          : 1184 (13177 expanded)
%              Number of equality atoms :   18 (  87 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ~ ( v2_struct_0 @ ( sk_C @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_zfmisc_1 @ X32 )
      | ( X33 = X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k1_tarski @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X37 ) @ X36 ) @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','49'])).

thf('51',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('52',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('54',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','52','53'])).

thf('55',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ( m1_pre_topc @ ( sk_C @ X34 @ X35 ) @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','54'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['73'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('75',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf(cc23_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B )
              & ( v2_tdlat_3 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('82',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( v2_tdlat_3 @ X27 )
      | ( v7_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc23_tex_2])).

thf('83',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('90',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_tdlat_3 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('99',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ( v1_tdlat_3 @ ( sk_C @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','52','53'])).

thf('111',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','88','97','111'])).

thf('113',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ( X34
        = ( u1_struct_0 @ ( sk_C @ X34 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['123','124'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('126',plain,(
    ! [X21: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( v7_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('127',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','52','53'])).

thf('129',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('131',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','52'])).

thf('132',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['129','132'])).

thf('134',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('135',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','136'])).

thf('138',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['113','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['60','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H8CZ8312HP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 177 iterations in 0.054s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.49  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.22/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.49  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(t44_tex_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.22/0.49         ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.49            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.49                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t34_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.49                ( ![C:$i]:
% 0.22/0.49                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.49                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X34 : $i, X35 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X34)
% 0.22/0.49          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.22/0.49          | ~ (v2_tex_2 @ X34 @ X35)
% 0.22/0.49          | ~ (v2_struct_0 @ (sk_C @ X34 @ X35))
% 0.22/0.49          | ~ (l1_pre_topc @ X35)
% 0.22/0.49          | ~ (v2_pre_topc @ X35)
% 0.22/0.49          | (v2_struct_0 @ X35))),
% 0.22/0.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.49  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['6'])).
% 0.22/0.49  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.49      inference('split', [status(esa)], ['8'])).
% 0.22/0.49  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['6'])).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf(l1_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X10 : $i, X12 : $i]:
% 0.22/0.49         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf(t1_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X32)
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X32)
% 0.22/0.49          | ((X33) = (X32))
% 0.22/0.49          | ~ (r1_tarski @ X33 @ X32)
% 0.22/0.49          | (v1_xboole_0 @ X33))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.22/0.49          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.22/0.49          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.22/0.49          | (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.49  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.49  thf('17', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0)
% 0.22/0.49          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i]:
% 0.22/0.49         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('21', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf(t1_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.49       ( r1_tarski @ A @ C ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.49          | ~ (r1_tarski @ X7 @ X8)
% 0.22/0.49          | (r1_tarski @ X6 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0)
% 0.22/0.49          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.22/0.49          | ~ (r1_tarski @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.49  thf('26', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((r2_hidden @ X10 @ X11) | ~ (r1_tarski @ (k1_tarski @ X10) @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.49  thf('29', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf(t1_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.49  thf('31', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf(t36_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 0.22/0.49          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X37) @ X36) @ X37)
% 0.22/0.49          | ~ (l1_pre_topc @ X37)
% 0.22/0.49          | ~ (v2_pre_topc @ X37)
% 0.22/0.49          | (v2_struct_0 @ X37))),
% 0.22/0.49      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.22/0.49           sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.22/0.49           sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.49  thf('37', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X22)
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ X22)
% 0.22/0.50          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.22/0.50          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.22/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.50  thf('42', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.22/0.50         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.22/0.50      inference('clc', [status(thm)], ['39', '42'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['36', '43'])).
% 0.22/0.50  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['18', '46'])).
% 0.22/0.50  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('49', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['8'])).
% 0.22/0.50  thf('52', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.50  thf('53', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.22/0.50      inference('split', [status(esa)], ['6'])).
% 0.22/0.50  thf('54', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['9', '52', '53'])).
% 0.22/0.50  thf('55', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['7', '54'])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '55'])).
% 0.22/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.50  thf('59', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('60', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['58', '59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X34)
% 0.22/0.50          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.22/0.50          | ~ (v2_tex_2 @ X34 @ X35)
% 0.22/0.50          | (m1_pre_topc @ (sk_C @ X34 @ X35) @ X35)
% 0.22/0.50          | ~ (l1_pre_topc @ X35)
% 0.22/0.50          | ~ (v2_pre_topc @ X35)
% 0.22/0.50          | (v2_struct_0 @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.22/0.50  thf('67', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['7', '54'])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.50  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['68', '69'])).
% 0.22/0.50  thf('71', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('72', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('74', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.22/0.50      inference('simplify', [status(thm)], ['73'])).
% 0.22/0.50  thf(t4_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.22/0.50                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X24 @ X25)
% 0.22/0.50          | ~ (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.22/0.50          | (m1_pre_topc @ X24 @ X26)
% 0.22/0.50          | ~ (m1_pre_topc @ X26 @ X25)
% 0.22/0.50          | ~ (l1_pre_topc @ X25)
% 0.22/0.50          | ~ (v2_pre_topc @ X25))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X1)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.50          | (m1_pre_topc @ X0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((m1_pre_topc @ X0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X1)
% 0.22/0.50          | ~ (v2_pre_topc @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['76'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['72', '77'])).
% 0.22/0.50  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.22/0.50  thf(cc23_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) & 
% 0.22/0.50               ( v2_tdlat_3 @ B ) ) =>
% 0.22/0.50             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('82', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X27 @ X28)
% 0.22/0.50          | ~ (v1_tdlat_3 @ X27)
% 0.22/0.50          | ~ (v2_tdlat_3 @ X27)
% 0.22/0.50          | (v7_struct_0 @ X27)
% 0.22/0.50          | (v2_struct_0 @ X27)
% 0.22/0.50          | ~ (l1_pre_topc @ X28)
% 0.22/0.50          | (v2_struct_0 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc23_tex_2])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.22/0.50  thf('84', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('85', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.50          | (l1_pre_topc @ X19)
% 0.22/0.50          | ~ (l1_pre_topc @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.22/0.50  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('88', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.50  thf('89', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf(cc6_tdlat_3, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.22/0.50         ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.22/0.50  thf('90', plain,
% 0.22/0.50      (![X30 : $i, X31 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X30 @ X31)
% 0.22/0.50          | (v2_tdlat_3 @ X30)
% 0.22/0.50          | ~ (l1_pre_topc @ X31)
% 0.22/0.50          | ~ (v2_tdlat_3 @ X31)
% 0.22/0.50          | ~ (v2_pre_topc @ X31)
% 0.22/0.50          | (v2_struct_0 @ X31))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.22/0.50  thf('91', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.50  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('93', plain, ((v2_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('95', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.22/0.50  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('97', plain, ((v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['95', '96'])).
% 0.22/0.50  thf('98', plain,
% 0.22/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['6'])).
% 0.22/0.50  thf('99', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('100', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X34)
% 0.22/0.50          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.22/0.50          | ~ (v2_tex_2 @ X34 @ X35)
% 0.22/0.50          | (v1_tdlat_3 @ (sk_C @ X34 @ X35))
% 0.22/0.50          | ~ (l1_pre_topc @ X35)
% 0.22/0.50          | ~ (v2_pre_topc @ X35)
% 0.22/0.50          | (v2_struct_0 @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.50  thf('101', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['99', '100'])).
% 0.22/0.50  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('104', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.22/0.50  thf('105', plain,
% 0.22/0.50      ((((v1_xboole_0 @ sk_B_1)
% 0.22/0.50         | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['98', '104'])).
% 0.22/0.50  thf('106', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('107', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.22/0.50         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['105', '106'])).
% 0.22/0.50  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('109', plain,
% 0.22/0.50      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.50         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['107', '108'])).
% 0.22/0.50  thf('110', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['9', '52', '53'])).
% 0.22/0.50  thf('111', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 0.22/0.50  thf('112', plain,
% 0.22/0.50      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['83', '88', '97', '111'])).
% 0.22/0.50  thf('113', plain,
% 0.22/0.50      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['112'])).
% 0.22/0.50  thf('114', plain,
% 0.22/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['6'])).
% 0.22/0.50  thf('115', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('116', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X34)
% 0.22/0.50          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.22/0.50          | ~ (v2_tex_2 @ X34 @ X35)
% 0.22/0.50          | ((X34) = (u1_struct_0 @ (sk_C @ X34 @ X35)))
% 0.22/0.50          | ~ (l1_pre_topc @ X35)
% 0.22/0.50          | ~ (v2_pre_topc @ X35)
% 0.22/0.50          | (v2_struct_0 @ X35))),
% 0.22/0.50      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.22/0.50  thf('117', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['115', '116'])).
% 0.22/0.50  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('120', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.22/0.50  thf('121', plain,
% 0.22/0.50      ((((v1_xboole_0 @ sk_B_1)
% 0.22/0.50         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.50         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['114', '120'])).
% 0.22/0.50  thf('122', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('123', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))))
% 0.22/0.50         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['121', '122'])).
% 0.22/0.50  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('125', plain,
% 0.22/0.50      ((((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.22/0.50         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['123', '124'])).
% 0.22/0.50  thf(fc7_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.50  thf('126', plain,
% 0.22/0.50      (![X21 : $i]:
% 0.22/0.50         ((v1_zfmisc_1 @ (u1_struct_0 @ X21))
% 0.22/0.50          | ~ (l1_struct_0 @ X21)
% 0.22/0.50          | ~ (v7_struct_0 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.22/0.50  thf('127', plain,
% 0.22/0.50      ((((v1_zfmisc_1 @ sk_B_1)
% 0.22/0.50         | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50         | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.22/0.50         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['125', '126'])).
% 0.22/0.50  thf('128', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['9', '52', '53'])).
% 0.22/0.50  thf('129', plain,
% 0.22/0.50      (((v1_zfmisc_1 @ sk_B_1)
% 0.22/0.50        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['127', '128'])).
% 0.22/0.50  thf('130', plain,
% 0.22/0.50      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['8'])).
% 0.22/0.50  thf('131', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['9', '52'])).
% 0.22/0.50  thf('132', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 0.22/0.50  thf('133', plain,
% 0.22/0.50      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['129', '132'])).
% 0.22/0.50  thf('134', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.50  thf(dt_l1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('135', plain,
% 0.22/0.50      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('136', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['134', '135'])).
% 0.22/0.50  thf('137', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['133', '136'])).
% 0.22/0.50  thf('138', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['113', '137'])).
% 0.22/0.50  thf('139', plain, ($false), inference('demod', [status(thm)], ['60', '138'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
