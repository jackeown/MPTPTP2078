%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PtaPvOX9C7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:34 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 125 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  427 ( 972 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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

thf('20',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ X16 )
       != ( sk_C @ X13 @ X14 ) )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( sk_C @ X13 @ X14 ) @ X13 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('44',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32','44'])).

thf('46',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['4','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PtaPvOX9C7
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 475 iterations in 0.250s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(t35_tex_2, conjecture,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.69           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i]:
% 0.46/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.69            ( l1_pre_topc @ A ) ) =>
% 0.46/0.69          ( ![B:$i]:
% 0.46/0.69            ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.69                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.69              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.46/0.69  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(l13_xboole_0, axiom,
% 0.46/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.69  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.69  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.69  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.69  thf(t4_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(cc2_pre_topc, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (![X11 : $i, X12 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.69          | (v4_pre_topc @ X11 @ X12)
% 0.46/0.69          | ~ (v1_xboole_0 @ X11)
% 0.46/0.69          | ~ (l1_pre_topc @ X12)
% 0.46/0.69          | ~ (v2_pre_topc @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.69  thf('10', plain, ((v1_xboole_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.69  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['9', '12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v4_pre_topc @ X0 @ X1)
% 0.46/0.69          | ~ (v1_xboole_0 @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X1)
% 0.46/0.69          | ~ (v2_pre_topc @ X1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['6', '13'])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_pre_topc @ sk_A)
% 0.46/0.69          | ~ (v1_xboole_0 @ X0)
% 0.46/0.69          | (v4_pre_topc @ X0 @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '14'])).
% 0.46/0.69  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.46/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(d6_tex_2, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ( v2_tex_2 @ B @ A ) <=>
% 0.46/0.69             ( ![C:$i]:
% 0.46/0.69               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.46/0.69                      ( ![D:$i]:
% 0.46/0.69                        ( ( m1_subset_1 @
% 0.46/0.69                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.46/0.69                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.46/0.69                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.69          | ~ (v4_pre_topc @ X16 @ X14)
% 0.46/0.69          | ((k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ X16)
% 0.46/0.69              != (sk_C @ X13 @ X14))
% 0.46/0.69          | (v2_tex_2 @ X13 @ X14)
% 0.46/0.69          | ~ (l1_pre_topc @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.69          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.46/0.69              != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.69          | ~ (v4_pre_topc @ X1 @ X0)
% 0.46/0.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.69          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.46/0.69              != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.69          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['18', '21'])).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.69         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.46/0.69          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.69      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.69           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.69  thf(t17_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.46/0.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.69  thf(t3_xboole_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.69          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.69          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.69        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.46/0.69        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['17', '29'])).
% 0.46/0.69  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.69          | (r1_tarski @ (sk_C @ X13 @ X14) @ X13)
% 0.46/0.69          | (v2_tex_2 @ X13 @ X14)
% 0.46/0.69          | ~ (l1_pre_topc @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ X0)
% 0.46/0.69          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.69          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.69          | ~ (l1_pre_topc @ X0)
% 0.46/0.69          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.69  thf('39', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.69  thf('41', plain,
% 0.46/0.69      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.46/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.69        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['37', '40'])).
% 0.46/0.69  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf('44', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.46/0.69  thf('45', plain,
% 0.46/0.69      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['30', '31', '32', '44'])).
% 0.46/0.69  thf('46', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.69  thf('47', plain, ($false), inference('demod', [status(thm)], ['4', '46'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
