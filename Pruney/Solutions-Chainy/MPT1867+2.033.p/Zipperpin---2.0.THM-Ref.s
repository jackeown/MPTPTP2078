%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1K9ON0o3vH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:30 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  450 ( 761 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
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

thf('17',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X8 @ X7 @ X7 )
        = X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
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
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26','44'])).

thf('46',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['4','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1K9ON0o3vH
% 0.14/0.36  % Computer   : n001.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:07:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 133 iterations in 0.091s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(t35_tex_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57            ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.57                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.39/0.57  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(l13_xboole_0, axiom,
% 0.39/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.57  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.57  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.57  thf(t4_subset_1, axiom,
% 0.39/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(cc2_pre_topc, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.57          | (v4_pre_topc @ X14 @ X15)
% 0.39/0.57          | ~ (v1_xboole_0 @ X14)
% 0.39/0.57          | ~ (l1_pre_topc @ X15)
% 0.39/0.57          | ~ (v2_pre_topc @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v1_xboole_0 @ X1)
% 0.39/0.57          | (v4_pre_topc @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((v4_pre_topc @ X1 @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | ~ (v1_xboole_0 @ X1))),
% 0.39/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57          | (v4_pre_topc @ X0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '11'])).
% 0.39/0.57  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.57  thf(d6_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.39/0.57                      ( ![D:$i]:
% 0.39/0.57                        ( ( m1_subset_1 @
% 0.39/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.57                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.57                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.39/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.39/0.57          | ~ (v4_pre_topc @ X19 @ X17)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.39/0.57              != (sk_C @ X16 @ X17))
% 0.39/0.57          | (v2_tex_2 @ X16 @ X17)
% 0.39/0.57          | ~ (l1_pre_topc @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (l1_pre_topc @ X0)
% 0.39/0.57          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.39/0.57              != (sk_C @ k1_xboole_0 @ X0))
% 0.39/0.57          | ~ (v4_pre_topc @ X1 @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.57              != (sk_C @ k1_xboole_0 @ X0))
% 0.39/0.57          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.57  thf(idempotence_k9_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.57         (((k9_subset_1 @ X8 @ X7 @ X7) = (X7))
% 0.39/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.57      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.39/0.57          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.39/0.57          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['19', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.39/0.57        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '23'])).
% 0.39/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.57  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.57  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.39/0.57          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.39/0.57          | (v2_tex_2 @ X16 @ X17)
% 0.39/0.57          | ~ (l1_pre_topc @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (l1_pre_topc @ X0)
% 0.39/0.57          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.57          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf(t12_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ((k2_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.39/0.57              = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.57  thf('32', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.57  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.57  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['34', '35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['31', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.57  thf('39', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '40'])).
% 0.39/0.57  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.57  thf('44', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['24', '25', '26', '44'])).
% 0.39/0.57  thf('46', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.39/0.57  thf('47', plain, ($false), inference('demod', [status(thm)], ['4', '46'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
