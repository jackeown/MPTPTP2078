%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y3Z5eB7OfE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 201 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  629 (2133 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t78_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
            <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tops_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v3_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('19',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X9 @ X10 ) @ X10 )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_tops_2 @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( v3_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','31','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['33','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y3Z5eB7OfE
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 44 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.21/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(t78_tops_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @
% 0.21/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_pre_topc @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @
% 0.21/0.47                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47              ( ( v1_tops_2 @ B @ A ) <=>
% 0.21/0.47                ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t78_tops_2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.21/0.47        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.21/0.47       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d1_tops_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @
% 0.21/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ( v1_tops_2 @ B @ A ) <=>
% 0.21/0.47             ( ![C:$i]:
% 0.21/0.47               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X9 @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.47          | (r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 0.21/0.47          | (v1_tops_2 @ X9 @ X10)
% 0.21/0.47          | ~ (l1_pre_topc @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)) | (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.21/0.47         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['8'])).
% 0.21/0.47  thf(d3_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ X0 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((![X0 : $i]:
% 0.21/0.47          ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.47         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((((v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47         | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.47         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t4_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.47          | (m1_subset_1 @ X4 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf(d5_pre_topc, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.47             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.47          | ~ (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.21/0.47          | (v3_pre_topc @ X7 @ X8)
% 0.21/0.47          | ~ (l1_pre_topc @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47        | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X9 @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.47          | ~ (v3_pre_topc @ (sk_C_1 @ X9 @ X10) @ X10)
% 0.21/0.47          | (v1_tops_2 @ X9 @ X10)
% 0.21/0.47          | ~ (l1_pre_topc @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      ((~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.47        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['21', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((((v1_tops_2 @ sk_B @ sk_A) | (v1_tops_2 @ sk_B @ sk_A)))
% 0.21/0.47         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A))
% 0.21/0.47         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.21/0.47       ~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain, (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.21/0.47  thf('33', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['8'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X9 @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.47          | ~ (v1_tops_2 @ X9 @ X10)
% 0.21/0.47          | ~ (r2_hidden @ X11 @ X9)
% 0.21/0.47          | (v3_pre_topc @ X11 @ X10)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.47          | ~ (l1_pre_topc @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | (v3_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.47          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | (v3_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.47          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      ((![X0 : $i]:
% 0.21/0.47          (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.47           | (v3_pre_topc @ X0 @ sk_A)
% 0.21/0.47           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.47         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '40'])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      ((![X0 : $i]: ((v3_pre_topc @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.47         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      ((![X0 : $i]:
% 0.21/0.47          ((r1_tarski @ sk_B @ X0) | (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A)))
% 0.21/0.47         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ sk_B @ X0)
% 0.21/0.47          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.47          | ~ (v3_pre_topc @ X7 @ X8)
% 0.21/0.47          | (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.21/0.47          | ~ (l1_pre_topc @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ sk_B @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.47          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.47  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ sk_B @ X0)
% 0.21/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.47          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      ((![X0 : $i]:
% 0.21/0.47          ((r1_tarski @ sk_B @ X0)
% 0.21/0.47           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.47           | (r1_tarski @ sk_B @ X0)))
% 0.21/0.47         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['44', '51'])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      ((![X0 : $i]:
% 0.21/0.47          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.47           | (r1_tarski @ sk_B @ X0)))
% 0.21/0.47         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.21/0.47       ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['8'])).
% 0.21/0.47  thf('55', plain, (((v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['2', '31', '54'])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.47          | (r1_tarski @ sk_B @ X0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['53', '55'])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('58', plain,
% 0.21/0.47      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.21/0.47        | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.47  thf('59', plain, ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.47  thf('60', plain, ($false), inference('demod', [status(thm)], ['33', '59'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
