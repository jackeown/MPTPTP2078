%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jRFDlsoBII

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:26 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 259 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  557 (2168 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['3','6'])).

thf('15',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('30',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_xboole_0
      = ( sk_C @ k1_xboole_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( k1_xboole_0
    = ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X20 )
       != ( sk_C @ X17 @ X18 ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 )
     != ( sk_C @ k1_xboole_0 @ sk_A ) )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( k1_xboole_0
    = ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( k1_xboole_0
    = ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','46','47','48'])).

thf('50',plain,
    ( ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('52',plain,(
    ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jRFDlsoBII
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:07:17 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 57 iterations in 0.029s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.25/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(t4_subset_1, axiom,
% 0.25/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.25/0.51  thf('0', plain,
% 0.25/0.51      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.51  thf(cc2_pre_topc, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      (![X15 : $i, X16 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.25/0.51          | (v4_pre_topc @ X15 @ X16)
% 0.25/0.51          | ~ (v1_xboole_0 @ X15)
% 0.25/0.51          | ~ (l1_pre_topc @ X16)
% 0.25/0.51          | ~ (v2_pre_topc @ X16))),
% 0.25/0.51      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v2_pre_topc @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.25/0.51          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.51  thf(t35_tex_2, conjecture,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( ( v1_xboole_0 @ B ) & 
% 0.25/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.51           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]:
% 0.25/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.51            ( l1_pre_topc @ A ) ) =>
% 0.25/0.51          ( ![B:$i]:
% 0.25/0.51            ( ( ( v1_xboole_0 @ B ) & 
% 0.25/0.51                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.51              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.25/0.51  thf('3', plain, ((v1_xboole_0 @ sk_B)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('4', plain, ((v1_xboole_0 @ sk_B)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(l13_xboole_0, axiom,
% 0.25/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.25/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.25/0.51  thf('6', plain, (((sk_B) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.51  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.51      inference('demod', [status(thm)], ['3', '6'])).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v2_pre_topc @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.25/0.51      inference('demod', [status(thm)], ['2', '7'])).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.51  thf(d6_tex_2, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( l1_pre_topc @ A ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51           ( ( v2_tex_2 @ B @ A ) <=>
% 0.25/0.51             ( ![C:$i]:
% 0.25/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.25/0.51                      ( ![D:$i]:
% 0.25/0.51                        ( ( m1_subset_1 @
% 0.25/0.51                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.25/0.51                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.25/0.51                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      (![X17 : $i, X18 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.25/0.51          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.25/0.51          | (v2_tex_2 @ X17 @ X18)
% 0.25/0.51          | ~ (l1_pre_topc @ X18))),
% 0.25/0.51      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (l1_pre_topc @ X0)
% 0.25/0.51          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.51  thf(t28_xboole_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (![X1 : $i, X2 : $i]:
% 0.25/0.51         (((k3_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.25/0.51  thf('13', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | ((k3_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.25/0.51              = (sk_C @ k1_xboole_0 @ X0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.25/0.51  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.51      inference('demod', [status(thm)], ['3', '6'])).
% 0.25/0.51  thf('15', plain,
% 0.25/0.51      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.51  thf(dt_k9_subset_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.51       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.51         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.25/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.25/0.51      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.25/0.51  thf('17', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.25/0.51          (k1_zfmisc_1 @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.25/0.51  thf('18', plain,
% 0.25/0.51      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.25/0.51  thf('19', plain,
% 0.25/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.51         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.25/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.25/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.25/0.51  thf('20', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.25/0.51           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.51  thf('21', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (m1_subset_1 @ (k3_xboole_0 @ X1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.25/0.51      inference('demod', [status(thm)], ['17', '20'])).
% 0.25/0.51  thf(cc1_subset_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.25/0.51  thf('22', plain,
% 0.25/0.51      (![X10 : $i, X11 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.25/0.51          | (v1_xboole_0 @ X10)
% 0.25/0.51          | ~ (v1_xboole_0 @ X11))),
% 0.25/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.25/0.51  thf('23', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (v1_xboole_0 @ X0)
% 0.25/0.51          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.51  thf('24', plain,
% 0.25/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.25/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.25/0.51  thf('25', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (v1_xboole_0 @ X1)
% 0.25/0.51          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.25/0.51  thf('26', plain,
% 0.25/0.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '25'])).
% 0.25/0.51  thf('27', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | ((k1_xboole_0) = (sk_C @ k1_xboole_0 @ X0)))),
% 0.25/0.51      inference('demod', [status(thm)], ['13', '26'])).
% 0.25/0.51  thf('28', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('29', plain, (((sk_B) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.51  thf('30', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.25/0.51  thf('31', plain,
% 0.25/0.51      ((((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['27', '30'])).
% 0.25/0.51  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('33', plain, (((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.51  thf('34', plain,
% 0.25/0.51      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.51  thf('35', plain,
% 0.25/0.51      (![X17 : $i, X18 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.25/0.51          | (m1_subset_1 @ (sk_C @ X17 @ X18) @ 
% 0.25/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.25/0.51          | (v2_tex_2 @ X17 @ X18)
% 0.25/0.51          | ~ (l1_pre_topc @ X18))),
% 0.25/0.51      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.25/0.51  thf('36', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (l1_pre_topc @ X0)
% 0.25/0.51          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.25/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.25/0.51  thf('37', plain,
% 0.25/0.51      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.25/0.51  thf('38', plain,
% 0.25/0.51      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.25/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.25/0.51          | ~ (v4_pre_topc @ X20 @ X18)
% 0.25/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.25/0.51              != (sk_C @ X17 @ X18))
% 0.25/0.51          | (v2_tex_2 @ X17 @ X18)
% 0.25/0.51          | ~ (l1_pre_topc @ X18))),
% 0.25/0.51      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.25/0.51  thf('39', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (l1_pre_topc @ X0)
% 0.25/0.51          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.25/0.51              != (sk_C @ k1_xboole_0 @ X0))
% 0.25/0.51          | ~ (v4_pre_topc @ X1 @ X0)
% 0.25/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.25/0.51  thf('40', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | ~ (v4_pre_topc @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.25/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.25/0.51              (sk_C @ k1_xboole_0 @ X0)) != (sk_C @ k1_xboole_0 @ X0))
% 0.25/0.51          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['36', '39'])).
% 0.25/0.51  thf('41', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.25/0.51            (sk_C @ k1_xboole_0 @ X0)) != (sk_C @ k1_xboole_0 @ X0))
% 0.25/0.51          | ~ (v4_pre_topc @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.25/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.25/0.51  thf('42', plain,
% 0.25/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)
% 0.25/0.51          != (sk_C @ k1_xboole_0 @ sk_A))
% 0.25/0.51        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.25/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.51        | ~ (v4_pre_topc @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['33', '41'])).
% 0.25/0.51  thf('43', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.25/0.51           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.51  thf('44', plain,
% 0.25/0.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '25'])).
% 0.25/0.51  thf('45', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.25/0.51  thf('46', plain, (((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.51  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('48', plain, (((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.51  thf('49', plain,
% 0.25/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.51        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.25/0.51        | ~ (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['42', '45', '46', '47', '48'])).
% 0.25/0.51  thf('50', plain,
% 0.25/0.51      ((~ (v4_pre_topc @ k1_xboole_0 @ sk_A) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.25/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.25/0.51  thf('51', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.25/0.51  thf('52', plain, (~ (v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.25/0.51      inference('clc', [status(thm)], ['50', '51'])).
% 0.25/0.51  thf('53', plain, ((~ (l1_pre_topc @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['8', '52'])).
% 0.25/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('56', plain, ($false),
% 0.25/0.51      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
