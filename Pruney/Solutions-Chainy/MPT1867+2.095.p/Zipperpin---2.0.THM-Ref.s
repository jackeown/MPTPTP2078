%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FiIh5XFWAI

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  604 ( 940 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc11_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v2_tdlat_3 @ B )
          & ( v1_tdlat_3 @ B )
          & ( v2_pre_topc @ B )
          & ( v1_pre_topc @ B )
          & ~ ( v2_struct_0 @ B )
          & ( m1_pre_topc @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v1_tdlat_3 @ ( sk_B @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v1_tdlat_3 @ X11 )
      | ( v2_tex_2 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tdlat_3 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ( v2_tex_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['37','38','39','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FiIh5XFWAI
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:20:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 114 iterations in 0.081s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(t35_tex_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(rc11_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ?[B:$i]:
% 0.20/0.52         ( ( v2_tdlat_3 @ B ) & ( v1_tdlat_3 @ B ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52           ( v1_pre_topc @ B ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.20/0.52           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         ((m1_pre_topc @ (sk_B @ X10) @ X10)
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         ((v1_tdlat_3 @ (sk_B @ X10))
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         ((m1_pre_topc @ (sk_B @ X10) @ X10)
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.52  thf(l17_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.52          | ~ (l1_pre_topc @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.52  thf(t26_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.52                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X11)
% 0.20/0.52          | ~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.52          | ((X13) != (u1_struct_0 @ X11))
% 0.20/0.52          | ~ (v1_tdlat_3 @ X11)
% 0.20/0.52          | (v2_tex_2 @ X13 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.52          | ~ (l1_pre_topc @ X12)
% 0.20/0.52          | (v2_struct_0 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X12)
% 0.20/0.52          | ~ (l1_pre_topc @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.52          | (v2_tex_2 @ (u1_struct_0 @ X11) @ X12)
% 0.20/0.52          | ~ (v1_tdlat_3 @ X11)
% 0.20/0.52          | ~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.52          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 0.20/0.52          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.52          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.52          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.52  thf(t4_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.52  thf(t28_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.52                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | ~ (v2_tex_2 @ X14 @ X15)
% 0.20/0.52          | ~ (r1_tarski @ X16 @ X14)
% 0.20/0.52          | (v2_tex_2 @ X16 @ X15)
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | ~ (l1_pre_topc @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_tex_2 @ X1 @ X0)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ (sk_B @ X0)))
% 0.20/0.52          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ (sk_B @ X0)))
% 0.20/0.52          | (v2_tex_2 @ X1 @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X10 : $i]:
% 0.20/0.52         (~ (v2_struct_0 @ (sk_B @ X10))
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf(l13_xboole_0, axiom,
% 0.20/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.52  thf('31', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.52  thf('34', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '36'])).
% 0.20/0.52  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('40', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('41', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '38', '39', '42'])).
% 0.20/0.52  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
