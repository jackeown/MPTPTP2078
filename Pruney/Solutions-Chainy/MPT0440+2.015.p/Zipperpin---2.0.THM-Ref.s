%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qbvofqDXO7

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:44 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 327 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   24
%              Number of atoms          :  706 (3684 expanded)
%              Number of equality atoms :   89 ( 508 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('0',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29
        = ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X29 @ X26 ) @ ( sk_C_2 @ X29 @ X26 ) ) @ X26 )
      | ( r2_hidden @ ( sk_C_2 @ X29 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k1_tarski @ ( k4_tarski @ X8 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ X0 @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_B ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['0','2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X22 @ X19 ) @ ( sk_D @ X22 @ X19 ) ) @ X19 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('24',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k1_tarski @ ( k4_tarski @ X8 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('35',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X22
        = ( k1_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X22 @ X19 ) @ X23 ) @ X19 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_C_3 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('47',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['21','47'])).

thf('49',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['19','48'])).

thf('50',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ( X29
        = ( k2_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ ( sk_C_2 @ X29 @ X26 ) ) @ X26 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X29 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['19','48'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['21','47'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qbvofqDXO7
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.93/2.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.93/2.10  % Solved by: fo/fo7.sh
% 1.93/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.10  % done 1456 iterations in 1.656s
% 1.93/2.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.93/2.10  % SZS output start Refutation
% 1.93/2.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.93/2.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.93/2.10  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.93/2.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.93/2.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.93/2.10  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.93/2.10  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.93/2.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.93/2.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.93/2.10  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.93/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.10  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.10  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.93/2.10  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.93/2.10  thf(t23_relat_1, conjecture,
% 1.93/2.10    (![A:$i,B:$i,C:$i]:
% 1.93/2.10     ( ( v1_relat_1 @ C ) =>
% 1.93/2.10       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 1.93/2.10         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 1.93/2.10           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 1.93/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.10    (~( ![A:$i,B:$i,C:$i]:
% 1.93/2.10        ( ( v1_relat_1 @ C ) =>
% 1.93/2.10          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 1.93/2.10            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 1.93/2.10              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 1.93/2.10    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 1.93/2.10  thf('0', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(d1_tarski, axiom,
% 1.93/2.10    (![A:$i,B:$i]:
% 1.93/2.10     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.93/2.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.93/2.10  thf('1', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.10         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 1.93/2.10      inference('cnf', [status(esa)], [d1_tarski])).
% 1.93/2.10  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.93/2.10      inference('simplify', [status(thm)], ['1'])).
% 1.93/2.10  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 1.93/2.10      inference('sup+', [status(thm)], ['0', '2'])).
% 1.93/2.10  thf(d5_relat_1, axiom,
% 1.93/2.10    (![A:$i,B:$i]:
% 1.93/2.10     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.93/2.10       ( ![C:$i]:
% 1.93/2.10         ( ( r2_hidden @ C @ B ) <=>
% 1.93/2.10           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.93/2.10  thf('4', plain,
% 1.93/2.10      (![X26 : $i, X29 : $i]:
% 1.93/2.10         (((X29) = (k2_relat_1 @ X26))
% 1.93/2.10          | (r2_hidden @ 
% 1.93/2.10             (k4_tarski @ (sk_D_2 @ X29 @ X26) @ (sk_C_2 @ X29 @ X26)) @ X26)
% 1.93/2.10          | (r2_hidden @ (sk_C_2 @ X29 @ X26) @ X29))),
% 1.93/2.10      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.93/2.10  thf('5', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(t34_zfmisc_1, axiom,
% 1.93/2.10    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.10     ( ( r2_hidden @
% 1.93/2.10         ( k4_tarski @ A @ B ) @ 
% 1.93/2.10         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 1.93/2.10       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 1.93/2.10  thf('6', plain,
% 1.93/2.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.93/2.10         (((X10) = (X11))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 1.93/2.10               (k2_zfmisc_1 @ (k1_tarski @ X8) @ (k1_tarski @ X11))))),
% 1.93/2.10      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 1.93/2.10  thf(t69_enumset1, axiom,
% 1.93/2.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.93/2.10  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 1.93/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.93/2.10  thf(t36_zfmisc_1, axiom,
% 1.93/2.10    (![A:$i,B:$i,C:$i]:
% 1.93/2.10     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 1.93/2.10         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 1.93/2.10       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 1.93/2.10         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 1.93/2.10  thf('8', plain,
% 1.93/2.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.93/2.10         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 1.93/2.10           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 1.93/2.10      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 1.93/2.10  thf('9', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 1.93/2.10           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 1.93/2.10      inference('sup+', [status(thm)], ['7', '8'])).
% 1.93/2.10  thf('10', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 1.93/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.93/2.10  thf('11', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.93/2.10           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 1.93/2.10      inference('demod', [status(thm)], ['9', '10'])).
% 1.93/2.10  thf('12', plain,
% 1.93/2.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.93/2.10         (((X10) = (X11))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 1.93/2.10               (k1_tarski @ (k4_tarski @ X8 @ X11))))),
% 1.93/2.10      inference('demod', [status(thm)], ['6', '11'])).
% 1.93/2.10  thf('13', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X0) = (sk_B)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['5', '12'])).
% 1.93/2.10  thf('14', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 1.93/2.10          | ((X0) = (k2_relat_1 @ sk_C_3))
% 1.93/2.10          | ((sk_C_2 @ X0 @ sk_C_3) = (sk_B)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['4', '13'])).
% 1.93/2.10  thf('15', plain,
% 1.93/2.10      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.93/2.10         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 1.93/2.10      inference('cnf', [status(esa)], [d1_tarski])).
% 1.93/2.10  thf('16', plain,
% 1.93/2.10      (![X0 : $i, X3 : $i]:
% 1.93/2.10         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['15'])).
% 1.93/2.10  thf('17', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B))
% 1.93/2.10          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 1.93/2.10          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['14', '16'])).
% 1.93/2.10  thf('18', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((X0) != (sk_B))
% 1.93/2.10          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 1.93/2.10          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B)))),
% 1.93/2.10      inference('eq_fact', [status(thm)], ['17'])).
% 1.93/2.10  thf('19', plain,
% 1.93/2.10      ((((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))
% 1.93/2.10        | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['18'])).
% 1.93/2.10  thf('20', plain,
% 1.93/2.10      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 1.93/2.10        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('21', plain,
% 1.93/2.10      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 1.93/2.10         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 1.93/2.10      inference('split', [status(esa)], ['20'])).
% 1.93/2.10  thf('22', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 1.93/2.10      inference('sup+', [status(thm)], ['0', '2'])).
% 1.93/2.10  thf(d4_relat_1, axiom,
% 1.93/2.10    (![A:$i,B:$i]:
% 1.93/2.10     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.93/2.10       ( ![C:$i]:
% 1.93/2.10         ( ( r2_hidden @ C @ B ) <=>
% 1.93/2.10           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.93/2.10  thf('23', plain,
% 1.93/2.10      (![X19 : $i, X22 : $i]:
% 1.93/2.10         (((X22) = (k1_relat_1 @ X19))
% 1.93/2.10          | (r2_hidden @ 
% 1.93/2.10             (k4_tarski @ (sk_C_1 @ X22 @ X19) @ (sk_D @ X22 @ X19)) @ X19)
% 1.93/2.10          | (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 1.93/2.10      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.93/2.10  thf('24', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('25', plain,
% 1.93/2.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.93/2.10         (((X9) = (X8))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 1.93/2.10               (k2_zfmisc_1 @ (k1_tarski @ X8) @ (k1_tarski @ X11))))),
% 1.93/2.10      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 1.93/2.10  thf('26', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.93/2.10           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 1.93/2.10      inference('demod', [status(thm)], ['9', '10'])).
% 1.93/2.10  thf('27', plain,
% 1.93/2.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.93/2.10         (((X9) = (X8))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 1.93/2.10               (k1_tarski @ (k4_tarski @ X8 @ X11))))),
% 1.93/2.10      inference('demod', [status(thm)], ['25', '26'])).
% 1.93/2.10  thf('28', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X1) = (sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['24', '27'])).
% 1.93/2.10  thf('29', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X0)
% 1.93/2.10          | ((X0) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10          | ((sk_C_1 @ X0 @ sk_C_3) = (sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['23', '28'])).
% 1.93/2.10  thf('30', plain,
% 1.93/2.10      (![X0 : $i, X3 : $i]:
% 1.93/2.10         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['15'])).
% 1.93/2.10  thf('31', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (sk_A))
% 1.93/2.10          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['29', '30'])).
% 1.93/2.10  thf('32', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((sk_A) != (X0))
% 1.93/2.10          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 1.93/2.10          | ((k1_tarski @ X0) = (k1_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('eq_fact', [status(thm)], ['31'])).
% 1.93/2.10  thf('33', plain,
% 1.93/2.10      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['32'])).
% 1.93/2.10  thf('34', plain,
% 1.93/2.10      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10        | ((sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) = (sk_A)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['32'])).
% 1.93/2.10  thf('35', plain,
% 1.93/2.10      (![X19 : $i, X22 : $i, X23 : $i]:
% 1.93/2.10         (((X22) = (k1_relat_1 @ X19))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X22 @ X19) @ X23) @ X19)
% 1.93/2.10          | ~ (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 1.93/2.10      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.93/2.10  thf('36', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10          | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 1.93/2.10               (k1_tarski @ sk_A))
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['34', '35'])).
% 1.93/2.10  thf('37', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ sk_A) @ sk_C_3) @ 
% 1.93/2.10             (k1_tarski @ sk_A))
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3))),
% 1.93/2.10      inference('simplify', [status(thm)], ['36'])).
% 1.93/2.10  thf('38', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['33', '37'])).
% 1.93/2.10  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.93/2.10      inference('simplify', [status(thm)], ['1'])).
% 1.93/2.10  thf('40', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('demod', [status(thm)], ['38', '39'])).
% 1.93/2.10  thf('41', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_3)
% 1.93/2.10          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['40'])).
% 1.93/2.10  thf('42', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 1.93/2.10      inference('sup-', [status(thm)], ['22', '41'])).
% 1.93/2.10  thf('43', plain,
% 1.93/2.10      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 1.93/2.10         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 1.93/2.10      inference('split', [status(esa)], ['20'])).
% 1.93/2.10  thf('44', plain,
% 1.93/2.10      ((((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_C_3)))
% 1.93/2.10         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['42', '43'])).
% 1.93/2.10  thf('45', plain, ((((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['44'])).
% 1.93/2.10  thf('46', plain,
% 1.93/2.10      (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))) | 
% 1.93/2.10       ~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 1.93/2.10      inference('split', [status(esa)], ['20'])).
% 1.93/2.10  thf('47', plain, (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 1.93/2.10      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 1.93/2.10  thf('48', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 1.93/2.10      inference('simpl_trail', [status(thm)], ['21', '47'])).
% 1.93/2.10  thf('49', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 1.93/2.10      inference('simplify_reflect-', [status(thm)], ['19', '48'])).
% 1.93/2.10  thf('50', plain,
% 1.93/2.10      (![X26 : $i, X29 : $i, X30 : $i]:
% 1.93/2.10         (((X29) = (k2_relat_1 @ X26))
% 1.93/2.10          | ~ (r2_hidden @ (k4_tarski @ X30 @ (sk_C_2 @ X29 @ X26)) @ X26)
% 1.93/2.10          | ~ (r2_hidden @ (sk_C_2 @ X29 @ X26) @ X29))),
% 1.93/2.10      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.93/2.10  thf('51', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 1.93/2.10          | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 1.93/2.10               (k1_tarski @ sk_B))
% 1.93/2.10          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['49', '50'])).
% 1.93/2.10  thf('52', plain, (((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B))),
% 1.93/2.10      inference('simplify_reflect-', [status(thm)], ['19', '48'])).
% 1.93/2.10  thf('53', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.93/2.10      inference('simplify', [status(thm)], ['1'])).
% 1.93/2.10  thf('54', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 1.93/2.10          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 1.93/2.10      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.93/2.10  thf('55', plain, (((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B))),
% 1.93/2.10      inference('simpl_trail', [status(thm)], ['21', '47'])).
% 1.93/2.10  thf('56', plain,
% 1.93/2.10      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)),
% 1.93/2.10      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 1.93/2.10  thf('57', plain, ($false), inference('sup-', [status(thm)], ['3', '56'])).
% 1.93/2.10  
% 1.93/2.10  % SZS output end Refutation
% 1.93/2.10  
% 1.93/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
