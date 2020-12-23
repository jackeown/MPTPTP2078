%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zR1t6bEjqo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:15 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 153 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :   20
%              Number of atoms          :  528 (1150 expanded)
%              Number of equality atoms :   42 ( 100 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X49: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X53 ) @ X54 )
      | ( ( k7_relat_1 @ X53 @ X54 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('13',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('21',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X42 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('29',plain,
    ( ( ( k9_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('30',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','25','29'])).

thf('31',plain,
    ( ( k9_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X52: $i] :
      ( ( r1_tarski @ X52 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('39',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) )
      | ~ ( r1_xboole_0 @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k7_relat_1 @ X53 @ X54 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X53 ) @ X54 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['27','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zR1t6bEjqo
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 328 iterations in 0.228s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.68  thf(t151_relat_1, conjecture,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.68         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i]:
% 0.48/0.68        ( ( v1_relat_1 @ B ) =>
% 0.48/0.68          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.68            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.48/0.68        | ((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.48/0.68         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.48/0.68       ~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf(fc11_relat_1, axiom,
% 0.48/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X49 : $i]:
% 0.48/0.68         ((v1_xboole_0 @ (k2_relat_1 @ X49)) | ~ (v1_xboole_0 @ X49))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.48/0.68  thf(l13_xboole_0, axiom,
% 0.48/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.48/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.48/0.68        | ((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.48/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['6'])).
% 0.48/0.68  thf(t95_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.68         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X53 : $i, X54 : $i]:
% 0.48/0.68         (~ (r1_xboole_0 @ (k1_relat_1 @ X53) @ X54)
% 0.48/0.68          | ((k7_relat_1 @ X53 @ X54) = (k1_xboole_0))
% 0.48/0.68          | ~ (v1_relat_1 @ X53))),
% 0.48/0.68      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (((~ (v1_relat_1 @ sk_B_1)
% 0.48/0.68         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.48/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.48/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.48/0.68  thf(t148_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X50 : $i, X51 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 0.48/0.68          | ~ (v1_relat_1 @ X50))),
% 0.48/0.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A))
% 0.48/0.68         | ~ (v1_relat_1 @ sk_B_1)))
% 0.48/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.68  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      ((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B_1 @ sk_A)))
% 0.48/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      ((((k9_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.48/0.68         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.48/0.68         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.48/0.68             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.48/0.68         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.48/0.68             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['5', '17'])).
% 0.48/0.68  thf(d1_xboole_0, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.68  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.48/0.68  thf('20', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.48/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.68  thf(t55_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.68         (~ (r1_xboole_0 @ (k2_tarski @ X42 @ X43) @ X44)
% 0.48/0.68          | ~ (r2_hidden @ X42 @ X44))),
% 0.48/0.68      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.48/0.68  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.68  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.68      inference('sup-', [status(thm)], ['19', '22'])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.48/0.68         <= (~ (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.48/0.68             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['18', '23'])).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.48/0.68       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.48/0.68      inference('simplify', [status(thm)], ['24'])).
% 0.48/0.68  thf('26', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.48/0.68      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.48/0.68  thf('27', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.48/0.68      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.48/0.68         <= ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.48/0.68      inference('split', [status(esa)], ['6'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.48/0.68       ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['6'])).
% 0.48/0.68  thf('30', plain, ((((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.48/0.68      inference('sat_resolution*', [status(thm)], ['2', '25', '29'])).
% 0.48/0.68  thf('31', plain, (((k9_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.48/0.68      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X50 : $i, X51 : $i]:
% 0.48/0.68         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 0.48/0.68          | ~ (v1_relat_1 @ X50))),
% 0.48/0.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.68  thf(t21_relat_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ A ) =>
% 0.48/0.68       ( r1_tarski @
% 0.48/0.68         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X52 : $i]:
% 0.48/0.68         ((r1_tarski @ X52 @ 
% 0.48/0.68           (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52)))
% 0.48/0.68          | ~ (v1_relat_1 @ X52))),
% 0.48/0.68      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.48/0.68           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.48/0.68            (k9_relat_1 @ X1 @ X0)))
% 0.48/0.68          | ~ (v1_relat_1 @ X1)
% 0.48/0.68          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.48/0.68  thf(dt_k7_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X47 : $i, X48 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X47) | (v1_relat_1 @ (k7_relat_1 @ X47 @ X48)))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v1_relat_1 @ X1)
% 0.48/0.68          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.48/0.68             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.48/0.68              (k9_relat_1 @ X1 @ X0))))),
% 0.48/0.68      inference('clc', [status(thm)], ['34', '35'])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (((r1_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.48/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) @ 
% 0.48/0.68          k1_xboole_0))
% 0.48/0.68        | ~ (v1_relat_1 @ sk_B_1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['31', '36'])).
% 0.48/0.68  thf('38', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.48/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.68  thf(t127_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.48/0.68       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.68         ((r1_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ (k2_zfmisc_1 @ X40 @ X41))
% 0.48/0.68          | ~ (r1_xboole_0 @ X39 @ X41))),
% 0.48/0.68      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.48/0.68          (k2_zfmisc_1 @ X1 @ k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.68  thf(t66_xboole_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.48/0.68       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      (![X10 : $i]: (((X10) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X10 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.68  thf('43', plain, ((v1_relat_1 @ sk_B_1)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('44', plain, ((r1_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0)),
% 0.48/0.68      inference('demod', [status(thm)], ['37', '42', '43'])).
% 0.48/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.68  thf('45', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.48/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.68  thf(d10_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.68  thf('46', plain,
% 0.48/0.68      (![X4 : $i, X6 : $i]:
% 0.48/0.68         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('47', plain,
% 0.48/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.48/0.68  thf('48', plain, (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['44', '47'])).
% 0.48/0.68  thf('49', plain,
% 0.48/0.68      (![X53 : $i, X54 : $i]:
% 0.48/0.68         (((k7_relat_1 @ X53 @ X54) != (k1_xboole_0))
% 0.48/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X53) @ X54)
% 0.48/0.68          | ~ (v1_relat_1 @ X53))),
% 0.48/0.68      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.48/0.68  thf('50', plain,
% 0.48/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.68        | ~ (v1_relat_1 @ sk_B_1)
% 0.48/0.68        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.48/0.68  thf('51', plain, ((v1_relat_1 @ sk_B_1)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('52', plain,
% 0.48/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.68        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.48/0.68  thf('53', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.48/0.68      inference('simplify', [status(thm)], ['52'])).
% 0.48/0.68  thf('54', plain, ($false), inference('demod', [status(thm)], ['27', '53'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
