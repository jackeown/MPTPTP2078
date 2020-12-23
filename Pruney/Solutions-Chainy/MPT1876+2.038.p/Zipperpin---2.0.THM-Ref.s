%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tkjmt4NC8r

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  216 (1340 expanded)
%              Number of leaves         :   40 ( 407 expanded)
%              Depth                    :   35
%              Number of atoms          : 1499 (13509 expanded)
%              Number of equality atoms :   29 ( 122 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
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
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('33',plain,(
    r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('37',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
    = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('49',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','52'])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('56',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ X0 ) ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('69',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('77',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['75','84'])).

thf('86',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','87'])).

thf('89',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','88'])).

thf('90',plain,(
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

thf('91',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( X27
        = ( u1_struct_0 @ ( sk_C_1 @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('97',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('98',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','87','97'])).

thf('99',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['96','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('105',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('106',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('108',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_pre_topc @ ( sk_C_1 @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
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
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('120',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

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

thf('123',plain,(
    ! [X22: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v1_tdlat_3 @ X22 )
      | ~ ( v2_tdlat_3 @ X22 )
      | ( v7_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('124',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('126',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['124','136'])).

thf('138',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('139',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('148',plain,(
    ! [X21: $i] :
      ( ~ ( v2_tdlat_3 @ X21 )
      | ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('149',plain,
    ( ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('151',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['137','146','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('161',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','87','97'])).

thf('167',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('169',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','87','97'])).

thf('172',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['170','171'])).

thf('173',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['106','167','172'])).

thf('174',plain,(
    $false ),
    inference(demod,[status(thm)],['89','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tkjmt4NC8r
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.66  % Solved by: fo/fo7.sh
% 0.21/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.66  % done 254 iterations in 0.158s
% 0.21/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.66  % SZS output start Refutation
% 0.21/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.66  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.66  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.66  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.66  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.66  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.66  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.66  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.66  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.66  thf(t44_tex_2, conjecture,
% 0.21/0.66    (![A:$i]:
% 0.21/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.66         ( l1_pre_topc @ A ) ) =>
% 0.21/0.66       ( ![B:$i]:
% 0.21/0.66         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.66             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.66           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.66    (~( ![A:$i]:
% 0.21/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.66            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.66          ( ![B:$i]:
% 0.21/0.66            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.66                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.66              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.66    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.21/0.66  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.66  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.66      inference('split', [status(esa)], ['0'])).
% 0.21/0.66  thf('2', plain,
% 0.21/0.66      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.66      inference('split', [status(esa)], ['0'])).
% 0.21/0.66  thf('3', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.66  thf('4', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.66      inference('split', [status(esa)], ['3'])).
% 0.21/0.66  thf(d1_xboole_0, axiom,
% 0.21/0.66    (![A:$i]:
% 0.21/0.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.66  thf('5', plain,
% 0.21/0.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.66  thf(t63_subset_1, axiom,
% 0.21/0.66    (![A:$i,B:$i]:
% 0.21/0.66     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.66       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.66  thf('6', plain,
% 0.21/0.66      (![X8 : $i, X9 : $i]:
% 0.21/0.66         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.21/0.66          | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.66      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.66  thf('7', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X0)
% 0.21/0.66          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.66  thf(t3_subset, axiom,
% 0.21/0.66    (![A:$i,B:$i]:
% 0.21/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.66  thf('8', plain,
% 0.21/0.66      (![X12 : $i, X13 : $i]:
% 0.21/0.66         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.66  thf('9', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.66  thf(t1_tex_2, axiom,
% 0.21/0.66    (![A:$i]:
% 0.21/0.66     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.66       ( ![B:$i]:
% 0.21/0.66         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.66           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.66  thf('10', plain,
% 0.21/0.66      (![X25 : $i, X26 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X25)
% 0.21/0.66          | ~ (v1_zfmisc_1 @ X25)
% 0.21/0.66          | ((X26) = (X25))
% 0.21/0.66          | ~ (r1_tarski @ X26 @ X25)
% 0.21/0.66          | (v1_xboole_0 @ X26))),
% 0.21/0.66      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.66  thf('11', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X0)
% 0.21/0.66          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.21/0.66          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.21/0.66          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.66          | (v1_xboole_0 @ X0))),
% 0.21/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.66  thf('12', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.66          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.21/0.66          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.21/0.66          | (v1_xboole_0 @ X0))),
% 0.21/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.66  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.66  thf('13', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.21/0.66      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.66  thf('14', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X0)
% 0.21/0.66          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.21/0.66          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.66  thf('15', plain,
% 0.21/0.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.66  thf('16', plain,
% 0.21/0.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.66  thf('17', plain,
% 0.21/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.66  thf('18', plain,
% 0.21/0.66      (![X12 : $i, X13 : $i]:
% 0.21/0.66         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.66  thf('19', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.66  thf(d3_tarski, axiom,
% 0.21/0.66    (![A:$i,B:$i]:
% 0.21/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.66  thf('20', plain,
% 0.21/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.66         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.66          | (r2_hidden @ X3 @ X5)
% 0.21/0.66          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.66  thf('21', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.66  thf('22', plain,
% 0.21/0.66      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.66        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.66      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.66  thf('23', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.66  thf('24', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.66  thf('25', plain,
% 0.21/0.66      (![X8 : $i, X9 : $i]:
% 0.21/0.66         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.21/0.66          | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.66      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.66  thf('26', plain,
% 0.21/0.66      ((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ 
% 0.21/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.66  thf('27', plain,
% 0.21/0.66      (![X12 : $i, X13 : $i]:
% 0.21/0.66         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.66  thf('28', plain,
% 0.21/0.66      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.66  thf('29', plain,
% 0.21/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.66         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.66          | (r2_hidden @ X3 @ X5)
% 0.21/0.66          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.66  thf('30', plain,
% 0.21/0.66      (![X0 : $i]:
% 0.21/0.66         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.66          | ~ (r2_hidden @ X0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.21/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.66  thf('31', plain,
% 0.21/0.66      (((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.21/0.66        | (r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.21/0.66           (u1_struct_0 @ sk_A)))),
% 0.21/0.66      inference('sup-', [status(thm)], ['15', '30'])).
% 0.21/0.66  thf('32', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.21/0.66      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.66  thf('33', plain,
% 0.21/0.66      ((r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.21/0.66        (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.66  thf(t1_subset, axiom,
% 0.21/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.66  thf('34', plain,
% 0.21/0.66      (![X10 : $i, X11 : $i]:
% 0.21/0.66         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.66  thf('35', plain,
% 0.21/0.66      ((m1_subset_1 @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 0.21/0.66        (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.66  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.66    (![A:$i,B:$i]:
% 0.21/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.66       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.66  thf('36', plain,
% 0.21/0.66      (![X19 : $i, X20 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X19)
% 0.21/0.66          | ~ (m1_subset_1 @ X20 @ X19)
% 0.21/0.66          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.21/0.66      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.66  thf('37', plain,
% 0.21/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.66          (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.21/0.66          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.21/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.66  thf('38', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.66  thf('39', plain,
% 0.21/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.66  thf('40', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.66  thf('41', plain,
% 0.21/0.66      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.66         (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 0.21/0.66         = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))),
% 0.21/0.66      inference('clc', [status(thm)], ['37', '40'])).
% 0.21/0.66  thf('42', plain,
% 0.21/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.66          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.21/0.66        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.66      inference('sup+', [status(thm)], ['14', '41'])).
% 0.21/0.66  thf('43', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.66  thf('44', plain,
% 0.21/0.66      (![X10 : $i, X11 : $i]:
% 0.21/0.66         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.66  thf('45', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.66  thf('46', plain,
% 0.21/0.66      (![X19 : $i, X20 : $i]:
% 0.21/0.66         ((v1_xboole_0 @ X19)
% 0.21/0.66          | ~ (m1_subset_1 @ X20 @ X19)
% 0.21/0.66          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.21/0.66      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.67  thf('47', plain,
% 0.21/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.67          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.21/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.67  thf('48', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.67  thf('49', plain,
% 0.21/0.67      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.67         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.21/0.67      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.67  thf('50', plain,
% 0.21/0.67      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.21/0.67          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 0.21/0.67        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('demod', [status(thm)], ['42', '49'])).
% 0.21/0.67  thf('51', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('52', plain,
% 0.21/0.67      ((~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.67        | ((k1_tarski @ (sk_B @ sk_B_1))
% 0.21/0.67            = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))),
% 0.21/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.67  thf('53', plain,
% 0.21/0.67      ((((k1_tarski @ (sk_B @ sk_B_1))
% 0.21/0.67          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))
% 0.21/0.67         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['4', '52'])).
% 0.21/0.67  thf('54', plain,
% 0.21/0.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.67  thf('55', plain,
% 0.21/0.67      (![X0 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.67  thf('56', plain,
% 0.21/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.67         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.67          | (r2_hidden @ X3 @ X5)
% 0.21/0.67          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.67  thf('57', plain,
% 0.21/0.67      (![X0 : $i, X1 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X0)
% 0.21/0.67          | (r2_hidden @ X1 @ X0)
% 0.21/0.67          | ~ (r2_hidden @ X1 @ (k1_tarski @ (sk_B @ X0))))),
% 0.21/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.67  thf('58', plain,
% 0.21/0.67      (![X0 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.21/0.67          | (r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ X0))) @ X0)
% 0.21/0.67          | (v1_xboole_0 @ X0))),
% 0.21/0.67      inference('sup-', [status(thm)], ['54', '57'])).
% 0.21/0.67  thf('59', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.21/0.67      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.67  thf('60', plain,
% 0.21/0.67      (![X0 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X0)
% 0.21/0.67          | (r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ X0))) @ X0))),
% 0.21/0.67      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.67  thf('61', plain,
% 0.21/0.67      (![X8 : $i, X9 : $i]:
% 0.21/0.67         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.21/0.67          | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.67      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.67  thf('62', plain,
% 0.21/0.67      (![X0 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X0)
% 0.21/0.67          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ X0)))) @ 
% 0.21/0.67             (k1_zfmisc_1 @ X0)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.67  thf('63', plain,
% 0.21/0.67      ((((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.67         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('sup+', [status(thm)], ['53', '62'])).
% 0.21/0.67  thf('64', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('65', plain,
% 0.21/0.67      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (k1_zfmisc_1 @ sk_B_1)))
% 0.21/0.67         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.67  thf('66', plain,
% 0.21/0.67      (![X12 : $i, X13 : $i]:
% 0.21/0.67         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.67  thf('67', plain,
% 0.21/0.67      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1))
% 0.21/0.67         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.67  thf('68', plain,
% 0.21/0.67      (![X25 : $i, X26 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X25)
% 0.21/0.67          | ~ (v1_zfmisc_1 @ X25)
% 0.21/0.67          | ((X26) = (X25))
% 0.21/0.67          | ~ (r1_tarski @ X26 @ X25)
% 0.21/0.67          | (v1_xboole_0 @ X26))),
% 0.21/0.67      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.67  thf('69', plain,
% 0.21/0.67      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.21/0.67         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.21/0.67         | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.67         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.67  thf('70', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('split', [status(esa)], ['3'])).
% 0.21/0.67  thf('71', plain,
% 0.21/0.67      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 0.21/0.67         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.21/0.67         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.67  thf('72', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.21/0.67      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.67  thf('73', plain,
% 0.21/0.67      ((((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))))
% 0.21/0.67         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('clc', [status(thm)], ['71', '72'])).
% 0.21/0.67  thf('74', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('75', plain,
% 0.21/0.67      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.21/0.67         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.67  thf('76', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.67  thf(t36_tex_2, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.67       ( ![B:$i]:
% 0.21/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.67           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.21/0.67  thf('77', plain,
% 0.21/0.67      (![X29 : $i, X30 : $i]:
% 0.21/0.67         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.21/0.67          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.21/0.67          | ~ (l1_pre_topc @ X30)
% 0.21/0.67          | ~ (v2_pre_topc @ X30)
% 0.21/0.67          | (v2_struct_0 @ X30))),
% 0.21/0.67      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.21/0.67  thf('78', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.67        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.67           sk_A))),
% 0.21/0.67      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.67  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('81', plain,
% 0.21/0.67      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.21/0.67         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.21/0.67      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.67  thf('82', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.21/0.67      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.21/0.67  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('84', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.21/0.67      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.67  thf('85', plain,
% 0.21/0.67      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.67      inference('sup+', [status(thm)], ['75', '84'])).
% 0.21/0.67  thf('86', plain,
% 0.21/0.67      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('split', [status(esa)], ['0'])).
% 0.21/0.67  thf('87', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.21/0.67      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.67  thf('88', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.21/0.67      inference('sat_resolution*', [status(thm)], ['2', '87'])).
% 0.21/0.67  thf('89', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.21/0.67      inference('simpl_trail', [status(thm)], ['1', '88'])).
% 0.21/0.67  thf('90', plain,
% 0.21/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf(t34_tex_2, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.67       ( ![B:$i]:
% 0.21/0.67         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.67           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.67                ( ![C:$i]:
% 0.21/0.67                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.67                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.67                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.67  thf('91', plain,
% 0.21/0.67      (![X27 : $i, X28 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X27)
% 0.21/0.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.67          | ~ (v2_tex_2 @ X27 @ X28)
% 0.21/0.67          | ((X27) = (u1_struct_0 @ (sk_C_1 @ X27 @ X28)))
% 0.21/0.67          | ~ (l1_pre_topc @ X28)
% 0.21/0.67          | ~ (v2_pre_topc @ X28)
% 0.21/0.67          | (v2_struct_0 @ X28))),
% 0.21/0.67      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.67  thf('92', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.67        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.67  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('95', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.21/0.67  thf('96', plain,
% 0.21/0.67      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('split', [status(esa)], ['3'])).
% 0.21/0.67  thf('97', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.21/0.67      inference('split', [status(esa)], ['3'])).
% 0.21/0.67  thf('98', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.67      inference('sat_resolution*', [status(thm)], ['2', '87', '97'])).
% 0.21/0.67  thf('99', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.67      inference('simpl_trail', [status(thm)], ['96', '98'])).
% 0.21/0.67  thf('100', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('demod', [status(thm)], ['95', '99'])).
% 0.21/0.67  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('102', plain,
% 0.21/0.67      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.67        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.21/0.67      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.67  thf('103', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('104', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.67  thf(fc7_struct_0, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.67       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.67  thf('105', plain,
% 0.21/0.67      (![X18 : $i]:
% 0.21/0.67         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.21/0.67          | ~ (l1_struct_0 @ X18)
% 0.21/0.67          | ~ (v7_struct_0 @ X18))),
% 0.21/0.67      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.21/0.67  thf('106', plain,
% 0.21/0.67      (((v1_zfmisc_1 @ sk_B_1)
% 0.21/0.67        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup+', [status(thm)], ['104', '105'])).
% 0.21/0.67  thf('107', plain,
% 0.21/0.67      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('split', [status(esa)], ['3'])).
% 0.21/0.67  thf('108', plain,
% 0.21/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('109', plain,
% 0.21/0.67      (![X27 : $i, X28 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X27)
% 0.21/0.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.67          | ~ (v2_tex_2 @ X27 @ X28)
% 0.21/0.67          | (m1_pre_topc @ (sk_C_1 @ X27 @ X28) @ X28)
% 0.21/0.67          | ~ (l1_pre_topc @ X28)
% 0.21/0.67          | ~ (v2_pre_topc @ X28)
% 0.21/0.67          | (v2_struct_0 @ X28))),
% 0.21/0.67      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.67  thf('110', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.67        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.67  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('113', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.21/0.67  thf('114', plain,
% 0.21/0.67      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.67         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.67         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['107', '113'])).
% 0.21/0.67  thf('115', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('116', plain,
% 0.21/0.67      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['114', '115'])).
% 0.21/0.67  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('118', plain,
% 0.21/0.67      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['116', '117'])).
% 0.21/0.67  thf(dt_m1_pre_topc, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( l1_pre_topc @ A ) =>
% 0.21/0.67       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.67  thf('119', plain,
% 0.21/0.67      (![X16 : $i, X17 : $i]:
% 0.21/0.67         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.67          | (l1_pre_topc @ X16)
% 0.21/0.67          | ~ (l1_pre_topc @ X17))),
% 0.21/0.67      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.67  thf('120', plain,
% 0.21/0.67      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['118', '119'])).
% 0.21/0.67  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('122', plain,
% 0.21/0.67      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['120', '121'])).
% 0.21/0.67  thf(cc2_tex_1, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( l1_pre_topc @ A ) =>
% 0.21/0.67       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.67           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.21/0.67         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.21/0.67  thf('123', plain,
% 0.21/0.67      (![X22 : $i]:
% 0.21/0.67         ((v2_struct_0 @ X22)
% 0.21/0.67          | ~ (v2_pre_topc @ X22)
% 0.21/0.67          | ~ (v1_tdlat_3 @ X22)
% 0.21/0.67          | ~ (v2_tdlat_3 @ X22)
% 0.21/0.67          | (v7_struct_0 @ X22)
% 0.21/0.67          | ~ (l1_pre_topc @ X22))),
% 0.21/0.67      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.21/0.67  thf('124', plain,
% 0.21/0.67      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.67  thf('125', plain,
% 0.21/0.67      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('split', [status(esa)], ['3'])).
% 0.21/0.67  thf('126', plain,
% 0.21/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('127', plain,
% 0.21/0.67      (![X27 : $i, X28 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X27)
% 0.21/0.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.67          | ~ (v2_tex_2 @ X27 @ X28)
% 0.21/0.67          | (v1_tdlat_3 @ (sk_C_1 @ X27 @ X28))
% 0.21/0.67          | ~ (l1_pre_topc @ X28)
% 0.21/0.67          | ~ (v2_pre_topc @ X28)
% 0.21/0.67          | (v2_struct_0 @ X28))),
% 0.21/0.67      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.67  thf('128', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.67        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('sup-', [status(thm)], ['126', '127'])).
% 0.21/0.67  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('131', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.21/0.67  thf('132', plain,
% 0.21/0.67      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.67         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['125', '131'])).
% 0.21/0.67  thf('133', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('134', plain,
% 0.21/0.67      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['132', '133'])).
% 0.21/0.67  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('136', plain,
% 0.21/0.67      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['134', '135'])).
% 0.21/0.67  thf('137', plain,
% 0.21/0.67      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['124', '136'])).
% 0.21/0.67  thf('138', plain,
% 0.21/0.67      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['116', '117'])).
% 0.21/0.67  thf(cc6_tdlat_3, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.67         ( l1_pre_topc @ A ) ) =>
% 0.21/0.67       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.21/0.67  thf('139', plain,
% 0.21/0.67      (![X23 : $i, X24 : $i]:
% 0.21/0.67         (~ (m1_pre_topc @ X23 @ X24)
% 0.21/0.67          | (v2_tdlat_3 @ X23)
% 0.21/0.67          | ~ (l1_pre_topc @ X24)
% 0.21/0.67          | ~ (v2_tdlat_3 @ X24)
% 0.21/0.67          | ~ (v2_pre_topc @ X24)
% 0.21/0.67          | (v2_struct_0 @ X24))),
% 0.21/0.67      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.21/0.67  thf('140', plain,
% 0.21/0.67      ((((v2_struct_0 @ sk_A)
% 0.21/0.67         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.67         | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.67         | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['138', '139'])).
% 0.21/0.67  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('142', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('144', plain,
% 0.21/0.67      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.21/0.67  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('146', plain,
% 0.21/0.67      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['144', '145'])).
% 0.21/0.67  thf('147', plain,
% 0.21/0.67      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['120', '121'])).
% 0.21/0.67  thf(cc2_tdlat_3, axiom,
% 0.21/0.67    (![A:$i]:
% 0.21/0.67     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.21/0.67  thf('148', plain,
% 0.21/0.67      (![X21 : $i]:
% 0.21/0.67         (~ (v2_tdlat_3 @ X21) | (v2_pre_topc @ X21) | ~ (l1_pre_topc @ X21))),
% 0.21/0.67      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.21/0.67  thf('149', plain,
% 0.21/0.67      ((((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.67  thf('150', plain,
% 0.21/0.67      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['144', '145'])).
% 0.21/0.67  thf('151', plain,
% 0.21/0.67      (((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['149', '150'])).
% 0.21/0.67  thf('152', plain,
% 0.21/0.67      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['137', '146', '151'])).
% 0.21/0.67  thf('153', plain,
% 0.21/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('154', plain,
% 0.21/0.67      (![X27 : $i, X28 : $i]:
% 0.21/0.67         ((v1_xboole_0 @ X27)
% 0.21/0.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.67          | ~ (v2_tex_2 @ X27 @ X28)
% 0.21/0.67          | ~ (v2_struct_0 @ (sk_C_1 @ X27 @ X28))
% 0.21/0.67          | ~ (l1_pre_topc @ X28)
% 0.21/0.67          | ~ (v2_pre_topc @ X28)
% 0.21/0.67          | (v2_struct_0 @ X28))),
% 0.21/0.67      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.21/0.67  thf('155', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.67        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('sup-', [status(thm)], ['153', '154'])).
% 0.21/0.67  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('158', plain,
% 0.21/0.67      (((v2_struct_0 @ sk_A)
% 0.21/0.67        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.67      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.21/0.67  thf('159', plain,
% 0.21/0.67      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.67         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.67         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['152', '158'])).
% 0.21/0.67  thf('160', plain,
% 0.21/0.67      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('split', [status(esa)], ['3'])).
% 0.21/0.67  thf('161', plain,
% 0.21/0.67      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.67         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.67         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['159', '160'])).
% 0.21/0.67  thf('162', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('163', plain,
% 0.21/0.67      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['161', '162'])).
% 0.21/0.67  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.67  thf('165', plain,
% 0.21/0.67      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('clc', [status(thm)], ['163', '164'])).
% 0.21/0.67  thf('166', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.67      inference('sat_resolution*', [status(thm)], ['2', '87', '97'])).
% 0.21/0.67  thf('167', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.21/0.67      inference('simpl_trail', [status(thm)], ['165', '166'])).
% 0.21/0.67  thf('168', plain,
% 0.21/0.67      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('demod', [status(thm)], ['120', '121'])).
% 0.21/0.67  thf(dt_l1_pre_topc, axiom,
% 0.21/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.67  thf('169', plain,
% 0.21/0.67      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.67  thf('170', plain,
% 0.21/0.67      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.67         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.67      inference('sup-', [status(thm)], ['168', '169'])).
% 0.21/0.67  thf('171', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.67      inference('sat_resolution*', [status(thm)], ['2', '87', '97'])).
% 0.21/0.67  thf('172', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.21/0.67      inference('simpl_trail', [status(thm)], ['170', '171'])).
% 0.21/0.67  thf('173', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.21/0.67      inference('demod', [status(thm)], ['106', '167', '172'])).
% 0.21/0.67  thf('174', plain, ($false), inference('demod', [status(thm)], ['89', '173'])).
% 0.21/0.67  
% 0.21/0.67  % SZS output end Refutation
% 0.21/0.67  
% 0.21/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
