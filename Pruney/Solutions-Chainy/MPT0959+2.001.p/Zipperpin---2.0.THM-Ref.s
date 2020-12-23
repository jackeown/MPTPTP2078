%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OY88BPqwix

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:32 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  609 ( 821 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t32_wellord2,conjecture,(
    ! [A: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ A ) )
      = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_wellord2 @ ( k1_tarski @ A ) )
        = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_wellord2])).

thf('0',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k1_tarski @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( X46
       != ( k1_wellord2 @ X45 ) )
      | ~ ( r2_hidden @ X47 @ X45 )
      | ~ ( r2_hidden @ X48 @ X45 )
      | ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ X46 )
      | ~ ( r1_tarski @ X47 @ X48 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('7',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X45 ) )
      | ~ ( r1_tarski @ X47 @ X48 )
      | ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ ( k1_wellord2 @ X45 ) )
      | ~ ( r2_hidden @ X48 @ X45 )
      | ~ ( r2_hidden @ X47 @ X45 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('9',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X47 @ X48 )
      | ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ ( k1_wellord2 @ X45 ) )
      | ~ ( r2_hidden @ X48 @ X45 )
      | ~ ( r2_hidden @ X47 @ X45 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
       != ( k1_wellord2 @ X45 ) )
      | ( ( k3_relat_1 @ X46 )
        = X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('19',plain,(
    ! [X45: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X45 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X45 ) )
        = X45 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X45: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X45 ) )
      = X45 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X37 @ X38 ) @ ( sk_D @ X37 @ X38 ) ) @ X38 )
      | ( r1_tarski @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 )
      | ( r2_hidden @ X42 @ ( k3_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X45: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X45 ) )
      = X45 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('33',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X37 @ X38 ) @ ( sk_D @ X37 @ X38 ) ) @ X38 )
      | ( r1_tarski @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('34',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ ( k3_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_D @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X37 @ X38 ) @ ( sk_D @ X37 @ X38 ) ) @ X37 )
      | ( r1_tarski @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','49'])).

thf('51',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OY88BPqwix
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 728 iterations in 0.330s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.60/0.78  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.60/0.78  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.60/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(t32_wellord2, conjecture,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.60/0.78       ( k1_tarski @ ( k4_tarski @ A @ A ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i]:
% 0.60/0.78        ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.60/0.78          ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t32_wellord2])).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.60/0.78         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(d10_xboole_0, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.78  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.78      inference('simplify', [status(thm)], ['1'])).
% 0.60/0.78  thf(l1_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i]:
% 0.60/0.78         ((r2_hidden @ X29 @ X30) | ~ (r1_tarski @ (k1_tarski @ X29) @ X30))),
% 0.60/0.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.60/0.78  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.78  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.78      inference('simplify', [status(thm)], ['1'])).
% 0.60/0.78  thf(d1_wellord2, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ B ) =>
% 0.60/0.78       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.60/0.78         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.60/0.78           ( ![C:$i,D:$i]:
% 0.60/0.78             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.60/0.78               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.60/0.78                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.60/0.78         (((X46) != (k1_wellord2 @ X45))
% 0.60/0.78          | ~ (r2_hidden @ X47 @ X45)
% 0.60/0.78          | ~ (r2_hidden @ X48 @ X45)
% 0.60/0.78          | (r2_hidden @ (k4_tarski @ X47 @ X48) @ X46)
% 0.60/0.78          | ~ (r1_tarski @ X47 @ X48)
% 0.60/0.78          | ~ (v1_relat_1 @ X46))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ (k1_wellord2 @ X45))
% 0.60/0.78          | ~ (r1_tarski @ X47 @ X48)
% 0.60/0.78          | (r2_hidden @ (k4_tarski @ X47 @ X48) @ (k1_wellord2 @ X45))
% 0.60/0.78          | ~ (r2_hidden @ X48 @ X45)
% 0.60/0.78          | ~ (r2_hidden @ X47 @ X45))),
% 0.60/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.60/0.78  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.60/0.78  thf('8', plain, (![X49 : $i]: (v1_relat_1 @ (k1_wellord2 @ X49))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.60/0.78         (~ (r1_tarski @ X47 @ X48)
% 0.60/0.78          | (r2_hidden @ (k4_tarski @ X47 @ X48) @ (k1_wellord2 @ X45))
% 0.60/0.78          | ~ (r2_hidden @ X48 @ X45)
% 0.60/0.78          | ~ (r2_hidden @ X47 @ X45))),
% 0.60/0.78      inference('demod', [status(thm)], ['7', '8'])).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.78          | ~ (r2_hidden @ X0 @ X1)
% 0.60/0.78          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['5', '9'])).
% 0.60/0.78  thf('11', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.60/0.78          | ~ (r2_hidden @ X0 @ X1))),
% 0.60/0.78      inference('simplify', [status(thm)], ['10'])).
% 0.60/0.78  thf('12', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['4', '11'])).
% 0.60/0.78  thf('13', plain,
% 0.60/0.78      (![X29 : $i, X31 : $i]:
% 0.60/0.78         ((r1_tarski @ (k1_tarski @ X29) @ X31) | ~ (r2_hidden @ X29 @ X31))),
% 0.60/0.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.60/0.78  thf('14', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (r1_tarski @ (k1_tarski @ (k4_tarski @ X0 @ X0)) @ 
% 0.60/0.78          (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.78  thf('15', plain,
% 0.60/0.78      (![X0 : $i, X2 : $i]:
% 0.60/0.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.78  thf('16', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (~ (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.60/0.78             (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 0.60/0.78          | ((k1_wellord2 @ (k1_tarski @ X0))
% 0.60/0.78              = (k1_tarski @ (k4_tarski @ X0 @ X0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.78  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.78  thf('18', plain,
% 0.60/0.78      (![X45 : $i, X46 : $i]:
% 0.60/0.78         (((X46) != (k1_wellord2 @ X45))
% 0.60/0.78          | ((k3_relat_1 @ X46) = (X45))
% 0.60/0.78          | ~ (v1_relat_1 @ X46))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.60/0.78  thf('19', plain,
% 0.60/0.78      (![X45 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ (k1_wellord2 @ X45))
% 0.60/0.78          | ((k3_relat_1 @ (k1_wellord2 @ X45)) = (X45)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.78  thf('20', plain, (![X49 : $i]: (v1_relat_1 @ (k1_wellord2 @ X49))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.60/0.78  thf('21', plain, (![X45 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X45)) = (X45))),
% 0.60/0.78      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.78  thf(d3_relat_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ A ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.78           ( ![C:$i,D:$i]:
% 0.60/0.78             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.60/0.78               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.60/0.78  thf('22', plain,
% 0.60/0.78      (![X37 : $i, X38 : $i]:
% 0.60/0.78         ((r2_hidden @ 
% 0.60/0.78           (k4_tarski @ (sk_C_1 @ X37 @ X38) @ (sk_D @ X37 @ X38)) @ X38)
% 0.60/0.78          | (r1_tarski @ X38 @ X37)
% 0.60/0.78          | ~ (v1_relat_1 @ X38))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.60/0.78  thf(t30_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ C ) =>
% 0.60/0.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.60/0.78         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.60/0.78           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.60/0.78  thf('23', plain,
% 0.60/0.78      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.60/0.78         (~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44)
% 0.60/0.78          | (r2_hidden @ X42 @ (k3_relat_1 @ X44))
% 0.60/0.78          | ~ (v1_relat_1 @ X44))),
% 0.60/0.78      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.60/0.78  thf('24', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | (r1_tarski @ X0 @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ X0)
% 0.60/0.78          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.78  thf('25', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.60/0.78          | (r1_tarski @ X0 @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ X0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['24'])).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.60/0.78          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.60/0.78      inference('sup+', [status(thm)], ['21', '25'])).
% 0.60/0.78  thf('27', plain, (![X49 : $i]: (v1_relat_1 @ (k1_wellord2 @ X49))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.60/0.78  thf('28', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.60/0.78      inference('demod', [status(thm)], ['26', '27'])).
% 0.60/0.78  thf(d1_tarski, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.60/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.60/0.78  thf('29', plain,
% 0.60/0.78      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X21 @ X20)
% 0.60/0.78          | ((X21) = (X18))
% 0.60/0.78          | ((X20) != (k1_tarski @ X18)))),
% 0.60/0.78      inference('cnf', [status(esa)], [d1_tarski])).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      (![X18 : $i, X21 : $i]:
% 0.60/0.78         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.78  thf('31', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | ((sk_C_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['28', '30'])).
% 0.60/0.78  thf('32', plain, (![X45 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X45)) = (X45))),
% 0.60/0.78      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.78  thf('33', plain,
% 0.60/0.78      (![X37 : $i, X38 : $i]:
% 0.60/0.78         ((r2_hidden @ 
% 0.60/0.78           (k4_tarski @ (sk_C_1 @ X37 @ X38) @ (sk_D @ X37 @ X38)) @ X38)
% 0.60/0.78          | (r1_tarski @ X38 @ X37)
% 0.60/0.78          | ~ (v1_relat_1 @ X38))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.60/0.78  thf('34', plain,
% 0.60/0.78      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.60/0.78         (~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44)
% 0.60/0.78          | (r2_hidden @ X43 @ (k3_relat_1 @ X44))
% 0.60/0.78          | ~ (v1_relat_1 @ X44))),
% 0.60/0.78      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.60/0.78  thf('35', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | (r1_tarski @ X0 @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ X0)
% 0.60/0.78          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.78  thf('36', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (sk_D @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.60/0.78          | (r1_tarski @ X0 @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ X0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.60/0.78          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.60/0.78      inference('sup+', [status(thm)], ['32', '36'])).
% 0.60/0.78  thf('38', plain, (![X49 : $i]: (v1_relat_1 @ (k1_wellord2 @ X49))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.60/0.78      inference('demod', [status(thm)], ['37', '38'])).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      (![X18 : $i, X21 : $i]:
% 0.60/0.78         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | ((sk_D @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.78  thf('42', plain,
% 0.60/0.78      (![X37 : $i, X38 : $i]:
% 0.60/0.78         (~ (r2_hidden @ 
% 0.60/0.78             (k4_tarski @ (sk_C_1 @ X37 @ X38) @ (sk_D @ X37 @ X38)) @ X37)
% 0.60/0.78          | (r1_tarski @ X38 @ X37)
% 0.60/0.78          | ~ (v1_relat_1 @ X38))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.60/0.78  thf('43', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (r2_hidden @ 
% 0.60/0.78             (k4_tarski @ (sk_C_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.60/0.78             X1)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.78  thf('44', plain, (![X49 : $i]: (v1_relat_1 @ (k1_wellord2 @ X49))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (r2_hidden @ 
% 0.60/0.78             (k4_tarski @ (sk_C_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.60/0.78             X1)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.60/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | ~ (r2_hidden @ 
% 0.60/0.78               (k4_tarski @ (sk_C_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ 
% 0.60/0.78                X0) @ 
% 0.60/0.78               X1))),
% 0.60/0.78      inference('simplify', [status(thm)], ['45'])).
% 0.60/0.78  thf('47', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['31', '46'])).
% 0.60/0.78  thf('48', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.60/0.78          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 0.60/0.78      inference('simplify', [status(thm)], ['47'])).
% 0.60/0.78  thf('49', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.60/0.78          (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['17', '48'])).
% 0.60/0.78  thf('50', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((k1_wellord2 @ (k1_tarski @ X0))
% 0.60/0.78           = (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 0.60/0.78      inference('demod', [status(thm)], ['16', '49'])).
% 0.60/0.78  thf('51', plain,
% 0.60/0.78      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.60/0.78         != (k1_wellord2 @ (k1_tarski @ sk_A)))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '50'])).
% 0.60/0.78  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
