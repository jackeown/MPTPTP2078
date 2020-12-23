%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zstd7CtPqJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:36 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   66 (  92 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  492 ( 992 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t63_setfam_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v3_setfam_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v3_setfam_1 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
             => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v3_setfam_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v3_setfam_1 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
               => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_setfam_1 @ X17 @ X16 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( v3_setfam_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( k1_zfmisc_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_zfmisc_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k1_zfmisc_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v3_setfam_1 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('29',plain,
    ( ( v3_setfam_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ~ ( v3_setfam_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_setfam_1 @ X17 @ X16 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['4','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zstd7CtPqJ
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.60/4.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.60/4.79  % Solved by: fo/fo7.sh
% 4.60/4.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.60/4.79  % done 7227 iterations in 4.354s
% 4.60/4.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.60/4.79  % SZS output start Refutation
% 4.60/4.79  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 4.60/4.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.60/4.79  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.60/4.79  thf(sk_B_type, type, sk_B: $i).
% 4.60/4.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.60/4.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.60/4.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.60/4.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.60/4.79  thf(sk_A_type, type, sk_A: $i).
% 4.60/4.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.60/4.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.60/4.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.60/4.79  thf(t63_setfam_1, conjecture,
% 4.60/4.79    (![A:$i]:
% 4.60/4.79     ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.60/4.79       ( ![B:$i]:
% 4.60/4.79         ( ( ( v3_setfam_1 @ B @ A ) & 
% 4.60/4.79             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 4.60/4.79           ( ![C:$i]:
% 4.60/4.79             ( ( ( v3_setfam_1 @ C @ A ) & 
% 4.60/4.79                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 4.60/4.79               ( v3_setfam_1 @
% 4.60/4.79                 ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ))).
% 4.60/4.79  thf(zf_stmt_0, negated_conjecture,
% 4.60/4.79    (~( ![A:$i]:
% 4.60/4.79        ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.60/4.79          ( ![B:$i]:
% 4.60/4.79            ( ( ( v3_setfam_1 @ B @ A ) & 
% 4.60/4.79                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 4.60/4.79              ( ![C:$i]:
% 4.60/4.79                ( ( ( v3_setfam_1 @ C @ A ) & 
% 4.60/4.79                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 4.60/4.79                  ( v3_setfam_1 @
% 4.60/4.79                    ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )),
% 4.60/4.79    inference('cnf.neg', [status(esa)], [t63_setfam_1])).
% 4.60/4.79  thf('0', plain,
% 4.60/4.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.79  thf(d13_setfam_1, axiom,
% 4.60/4.79    (![A:$i,B:$i]:
% 4.60/4.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.60/4.79       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 4.60/4.79  thf('1', plain,
% 4.60/4.79      (![X16 : $i, X17 : $i]:
% 4.60/4.79         (~ (v3_setfam_1 @ X17 @ X16)
% 4.60/4.79          | ~ (r2_hidden @ X16 @ X17)
% 4.60/4.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 4.60/4.79      inference('cnf', [status(esa)], [d13_setfam_1])).
% 4.60/4.79  thf('2', plain,
% 4.60/4.79      ((~ (r2_hidden @ sk_A @ sk_C_1) | ~ (v3_setfam_1 @ sk_C_1 @ sk_A))),
% 4.60/4.79      inference('sup-', [status(thm)], ['0', '1'])).
% 4.60/4.79  thf('3', plain, ((v3_setfam_1 @ sk_C_1 @ sk_A)),
% 4.60/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.79  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 4.60/4.79      inference('demod', [status(thm)], ['2', '3'])).
% 4.60/4.79  thf(d3_tarski, axiom,
% 4.60/4.79    (![A:$i,B:$i]:
% 4.60/4.79     ( ( r1_tarski @ A @ B ) <=>
% 4.60/4.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.60/4.79  thf('5', plain,
% 4.60/4.79      (![X1 : $i, X3 : $i]:
% 4.60/4.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.60/4.79      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.80  thf(d3_xboole_0, axiom,
% 4.60/4.80    (![A:$i,B:$i,C:$i]:
% 4.60/4.80     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 4.60/4.80       ( ![D:$i]:
% 4.60/4.80         ( ( r2_hidden @ D @ C ) <=>
% 4.60/4.80           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.60/4.80  thf('6', plain,
% 4.60/4.80      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.60/4.80         (~ (r2_hidden @ X8 @ X6)
% 4.60/4.80          | (r2_hidden @ X8 @ X7)
% 4.60/4.80          | (r2_hidden @ X8 @ X5)
% 4.60/4.80          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 4.60/4.80      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.60/4.80  thf('7', plain,
% 4.60/4.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 4.60/4.80         ((r2_hidden @ X8 @ X5)
% 4.60/4.80          | (r2_hidden @ X8 @ X7)
% 4.60/4.80          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 4.60/4.80      inference('simplify', [status(thm)], ['6'])).
% 4.60/4.80  thf('8', plain,
% 4.60/4.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.80         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 4.60/4.80          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 4.60/4.80          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 4.60/4.80      inference('sup-', [status(thm)], ['5', '7'])).
% 4.60/4.80  thf('9', plain,
% 4.60/4.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf(t3_subset, axiom,
% 4.60/4.80    (![A:$i,B:$i]:
% 4.60/4.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.60/4.80  thf('10', plain,
% 4.60/4.80      (![X18 : $i, X19 : $i]:
% 4.60/4.80         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 4.60/4.80      inference('cnf', [status(esa)], [t3_subset])).
% 4.60/4.80  thf('11', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.60/4.80      inference('sup-', [status(thm)], ['9', '10'])).
% 4.60/4.80  thf('12', plain,
% 4.60/4.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.80         (~ (r2_hidden @ X0 @ X1)
% 4.60/4.80          | (r2_hidden @ X0 @ X2)
% 4.60/4.80          | ~ (r1_tarski @ X1 @ X2))),
% 4.60/4.80      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.80  thf('13', plain,
% 4.60/4.80      (![X0 : $i]:
% 4.60/4.80         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 4.60/4.80      inference('sup-', [status(thm)], ['11', '12'])).
% 4.60/4.80  thf('14', plain,
% 4.60/4.80      (![X0 : $i, X1 : $i]:
% 4.60/4.80         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_B @ X0)) @ X0)
% 4.60/4.80          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ X1)
% 4.60/4.80          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_B @ X0)) @ 
% 4.60/4.80             (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('sup-', [status(thm)], ['8', '13'])).
% 4.60/4.80  thf('15', plain,
% 4.60/4.80      (![X1 : $i, X3 : $i]:
% 4.60/4.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.60/4.80      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.80  thf('16', plain,
% 4.60/4.80      (![X0 : $i]:
% 4.60/4.80         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))
% 4.60/4.80          | (r2_hidden @ 
% 4.60/4.80             (sk_C @ (k1_zfmisc_1 @ sk_A) @ (k2_xboole_0 @ sk_B @ X0)) @ X0)
% 4.60/4.80          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('sup-', [status(thm)], ['14', '15'])).
% 4.60/4.80  thf('17', plain,
% 4.60/4.80      (![X0 : $i]:
% 4.60/4.80         ((r2_hidden @ 
% 4.60/4.80           (sk_C @ (k1_zfmisc_1 @ sk_A) @ (k2_xboole_0 @ sk_B @ X0)) @ X0)
% 4.60/4.80          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('simplify', [status(thm)], ['16'])).
% 4.60/4.80  thf('18', plain,
% 4.60/4.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf('19', plain,
% 4.60/4.80      (![X18 : $i, X19 : $i]:
% 4.60/4.80         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 4.60/4.80      inference('cnf', [status(esa)], [t3_subset])).
% 4.60/4.80  thf('20', plain, ((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.60/4.80      inference('sup-', [status(thm)], ['18', '19'])).
% 4.60/4.80  thf('21', plain,
% 4.60/4.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.80         (~ (r2_hidden @ X0 @ X1)
% 4.60/4.80          | (r2_hidden @ X0 @ X2)
% 4.60/4.80          | ~ (r1_tarski @ X1 @ X2))),
% 4.60/4.80      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.80  thf('22', plain,
% 4.60/4.80      (![X0 : $i]:
% 4.60/4.80         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.60/4.80      inference('sup-', [status(thm)], ['20', '21'])).
% 4.60/4.80  thf('23', plain,
% 4.60/4.80      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))
% 4.60/4.80        | (r2_hidden @ 
% 4.60/4.80           (sk_C @ (k1_zfmisc_1 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C_1)) @ 
% 4.60/4.80           (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('sup-', [status(thm)], ['17', '22'])).
% 4.60/4.80  thf('24', plain,
% 4.60/4.80      (![X1 : $i, X3 : $i]:
% 4.60/4.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.60/4.80      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.80  thf('25', plain,
% 4.60/4.80      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 4.60/4.80      inference('clc', [status(thm)], ['23', '24'])).
% 4.60/4.80  thf('26', plain,
% 4.60/4.80      (![X18 : $i, X20 : $i]:
% 4.60/4.80         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 4.60/4.80      inference('cnf', [status(esa)], [t3_subset])).
% 4.60/4.80  thf('27', plain,
% 4.60/4.80      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 4.60/4.80        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('sup-', [status(thm)], ['25', '26'])).
% 4.60/4.80  thf('28', plain,
% 4.60/4.80      (![X16 : $i, X17 : $i]:
% 4.60/4.80         ((r2_hidden @ X16 @ X17)
% 4.60/4.80          | (v3_setfam_1 @ X17 @ X16)
% 4.60/4.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 4.60/4.80      inference('cnf', [status(esa)], [d13_setfam_1])).
% 4.60/4.80  thf('29', plain,
% 4.60/4.80      (((v3_setfam_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 4.60/4.80        | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 4.60/4.80      inference('sup-', [status(thm)], ['27', '28'])).
% 4.60/4.80  thf('30', plain,
% 4.60/4.80      (~ (v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1) @ 
% 4.60/4.80          sk_A)),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf('31', plain,
% 4.60/4.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf('32', plain,
% 4.60/4.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf(redefinition_k4_subset_1, axiom,
% 4.60/4.80    (![A:$i,B:$i,C:$i]:
% 4.60/4.80     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.60/4.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.60/4.80       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.60/4.80  thf('33', plain,
% 4.60/4.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.60/4.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.60/4.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 4.60/4.80          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 4.60/4.80      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.60/4.80  thf('34', plain,
% 4.60/4.80      (![X0 : $i]:
% 4.60/4.80         (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0)
% 4.60/4.80            = (k2_xboole_0 @ sk_B @ X0))
% 4.60/4.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 4.60/4.80      inference('sup-', [status(thm)], ['32', '33'])).
% 4.60/4.80  thf('35', plain,
% 4.60/4.80      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1)
% 4.60/4.80         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 4.60/4.80      inference('sup-', [status(thm)], ['31', '34'])).
% 4.60/4.80  thf('36', plain, (~ (v3_setfam_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 4.60/4.80      inference('demod', [status(thm)], ['30', '35'])).
% 4.60/4.80  thf('37', plain, ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 4.60/4.80      inference('clc', [status(thm)], ['29', '36'])).
% 4.60/4.80  thf('38', plain,
% 4.60/4.80      (![X5 : $i, X7 : $i, X8 : $i]:
% 4.60/4.80         ((r2_hidden @ X8 @ X5)
% 4.60/4.80          | (r2_hidden @ X8 @ X7)
% 4.60/4.80          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 4.60/4.80      inference('simplify', [status(thm)], ['6'])).
% 4.60/4.80  thf('39', plain, (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_C_1))),
% 4.60/4.80      inference('sup-', [status(thm)], ['37', '38'])).
% 4.60/4.80  thf('40', plain,
% 4.60/4.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf('41', plain,
% 4.60/4.80      (![X16 : $i, X17 : $i]:
% 4.60/4.80         (~ (v3_setfam_1 @ X17 @ X16)
% 4.60/4.80          | ~ (r2_hidden @ X16 @ X17)
% 4.60/4.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 4.60/4.80      inference('cnf', [status(esa)], [d13_setfam_1])).
% 4.60/4.80  thf('42', plain,
% 4.60/4.80      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 4.60/4.80      inference('sup-', [status(thm)], ['40', '41'])).
% 4.60/4.80  thf('43', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 4.60/4.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.80  thf('44', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 4.60/4.80      inference('demod', [status(thm)], ['42', '43'])).
% 4.60/4.80  thf('45', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 4.60/4.80      inference('clc', [status(thm)], ['39', '44'])).
% 4.60/4.80  thf('46', plain, ($false), inference('demod', [status(thm)], ['4', '45'])).
% 4.60/4.80  
% 4.60/4.80  % SZS output end Refutation
% 4.60/4.80  
% 4.60/4.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
