%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oPWit3a9Mw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:25 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 191 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  614 (1832 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k1_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('16',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('24',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k1_tops_1 @ X43 @ X42 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X42 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tops_1 @ X42 @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('43',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','31','42'])).

thf('44',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','44'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['33','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oPWit3a9Mw
% 0.14/0.36  % Computer   : n003.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:45:27 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 1012 iterations in 0.291s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.58/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.58/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.58/0.77  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.58/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(t88_tops_1, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.77             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( l1_pre_topc @ A ) =>
% 0.58/0.77          ( ![B:$i]:
% 0.58/0.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77              ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.77                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.77         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('split', [status(esa)], ['0'])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.58/0.77       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.77      inference('split', [status(esa)], ['0'])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t74_tops_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( k1_tops_1 @ A @ B ) =
% 0.58/0.77             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X40 : $i, X41 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.58/0.77          | ((k1_tops_1 @ X41 @ X40)
% 0.58/0.77              = (k7_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 0.58/0.77                 (k2_tops_1 @ X41 @ X40)))
% 0.58/0.77          | ~ (l1_pre_topc @ X41))),
% 0.58/0.77      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.77        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.77               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.77  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.77            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(redefinition_k7_subset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.58/0.77          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k4_xboole_0 @ X30 @ X32)))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.77           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.77  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.77        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('split', [status(esa)], ['13'])).
% 0.58/0.77  thf(t10_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (r1_tarski @ sk_B @ (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['12', '16'])).
% 0.58/0.77  thf(t43_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.58/0.77       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.58/0.77          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (r1_tarski @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.77  thf(t38_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.58/0.77       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X13 : $i, X14 : $i]:
% 0.58/0.77         (((X13) = (k1_xboole_0))
% 0.58/0.77          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['11', '21'])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t84_tops_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.77             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X42 : $i, X43 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.58/0.77          | ((k1_tops_1 @ X43 @ X42) != (k1_xboole_0))
% 0.58/0.77          | (v2_tops_1 @ X42 @ X43)
% 0.58/0.77          | ~ (l1_pre_topc @ X43))),
% 0.58/0.77      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.77        | (v2_tops_1 @ sk_B @ sk_A)
% 0.58/0.77        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.77  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (((v2_tops_1 @ sk_B @ sk_A)
% 0.58/0.77        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['22', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      (((v2_tops_1 @ sk_B @ sk_A))
% 0.58/0.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['28'])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['0'])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.58/0.77       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('32', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.58/0.77  thf('33', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['13'])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X42 : $i, X43 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.58/0.77          | ~ (v2_tops_1 @ X42 @ X43)
% 0.58/0.77          | ((k1_tops_1 @ X43 @ X42) = (k1_xboole_0))
% 0.58/0.77          | ~ (l1_pre_topc @ X43))),
% 0.58/0.77      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.77        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.58/0.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.58/0.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['38', '39'])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.77         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['35', '40'])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.58/0.77       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('split', [status(esa)], ['13'])).
% 0.58/0.77  thf('43', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)], ['2', '31', '42'])).
% 0.58/0.77  thf('44', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '44'])).
% 0.58/0.77  thf(t48_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.58/0.77           = (k3_xboole_0 @ X20 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.58/0.77         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['45', '46'])).
% 0.58/0.77  thf(t3_boole, axiom,
% 0.58/0.77    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.77  thf('48', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['47', '48'])).
% 0.58/0.77  thf(commutativity_k2_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i]:
% 0.58/0.77         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.58/0.77      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.77  thf(t12_setfam_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      (![X33 : $i, X34 : $i]:
% 0.58/0.77         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['50', '51'])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (![X33 : $i, X34 : $i]:
% 0.58/0.77         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['52', '53'])).
% 0.58/0.77  thf(t17_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.58/0.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.77      inference('sup+', [status(thm)], ['54', '55'])).
% 0.58/0.77  thf('57', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['49', '56'])).
% 0.58/0.77  thf('58', plain, ($false), inference('demod', [status(thm)], ['33', '57'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
