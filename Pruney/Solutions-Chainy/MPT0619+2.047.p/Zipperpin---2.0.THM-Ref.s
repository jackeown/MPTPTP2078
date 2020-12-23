%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bqAz9m3H1a

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:26 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 114 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  613 (1009 expanded)
%              Number of equality atoms :   42 (  86 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( X23
       != ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X24 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('7',plain,(
    ! [X21: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X24 @ X21 ) @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ~ ( r1_tarski @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( X23
       != ( k2_relat_1 @ X21 ) )
      | ( X24
        = ( k1_funct_1 @ X21 @ ( sk_D_1 @ X24 @ X21 ) ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,(
    ! [X21: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( k2_relat_1 @ X21 ) )
      | ( X24
        = ( k1_funct_1 @ X21 @ ( sk_D_1 @ X24 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k9_relat_1 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['46','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bqAz9m3H1a
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.44  % Solved by: fo/fo7.sh
% 1.20/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.44  % done 918 iterations in 0.993s
% 1.20/1.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.44  % SZS output start Refutation
% 1.20/1.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.20/1.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.20/1.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.44  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.20/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.20/1.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.20/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.20/1.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.20/1.44  thf(t69_enumset1, axiom,
% 1.20/1.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.20/1.44  thf('0', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 1.20/1.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.20/1.44  thf(t12_zfmisc_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.20/1.44  thf('1', plain,
% 1.20/1.44      (![X13 : $i, X14 : $i]:
% 1.20/1.44         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X14))),
% 1.20/1.44      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.20/1.44  thf('2', plain,
% 1.20/1.44      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 1.20/1.44      inference('sup+', [status(thm)], ['0', '1'])).
% 1.20/1.44  thf(l1_zfmisc_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.20/1.44  thf('3', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i]:
% 1.20/1.44         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 1.20/1.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.20/1.44  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['2', '3'])).
% 1.20/1.44  thf(d3_tarski, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( r1_tarski @ A @ B ) <=>
% 1.20/1.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.20/1.44  thf('5', plain,
% 1.20/1.44      (![X1 : $i, X3 : $i]:
% 1.20/1.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.20/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.44  thf(d5_funct_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.44       ( ![B:$i]:
% 1.20/1.44         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.20/1.44           ( ![C:$i]:
% 1.20/1.44             ( ( r2_hidden @ C @ B ) <=>
% 1.20/1.44               ( ?[D:$i]:
% 1.20/1.44                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.20/1.44                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.20/1.44  thf('6', plain,
% 1.20/1.44      (![X21 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X23) != (k2_relat_1 @ X21))
% 1.20/1.44          | (r2_hidden @ (sk_D_1 @ X24 @ X21) @ (k1_relat_1 @ X21))
% 1.20/1.44          | ~ (r2_hidden @ X24 @ X23)
% 1.20/1.44          | ~ (v1_funct_1 @ X21)
% 1.20/1.44          | ~ (v1_relat_1 @ X21))),
% 1.20/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.20/1.44  thf('7', plain,
% 1.20/1.44      (![X21 : $i, X24 : $i]:
% 1.20/1.44         (~ (v1_relat_1 @ X21)
% 1.20/1.44          | ~ (v1_funct_1 @ X21)
% 1.20/1.44          | ~ (r2_hidden @ X24 @ (k2_relat_1 @ X21))
% 1.20/1.44          | (r2_hidden @ (sk_D_1 @ X24 @ X21) @ (k1_relat_1 @ X21)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['6'])).
% 1.20/1.44  thf('8', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.20/1.44          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.20/1.44             (k1_relat_1 @ X0))
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['5', '7'])).
% 1.20/1.44  thf('9', plain,
% 1.20/1.44      (![X5 : $i, X7 : $i]:
% 1.20/1.44         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 1.20/1.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.20/1.44  thf('10', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         (~ (v1_relat_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.20/1.44          | (r1_tarski @ 
% 1.20/1.44             (k1_tarski @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) @ 
% 1.20/1.44             (k1_relat_1 @ X0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['8', '9'])).
% 1.20/1.44  thf(t14_funct_1, conjecture,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.44       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.20/1.44         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.20/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.44    (~( ![A:$i,B:$i]:
% 1.20/1.44        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.44          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.20/1.44            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 1.20/1.44    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 1.20/1.44  thf('11', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(t6_zfmisc_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 1.20/1.44       ( ( A ) = ( B ) ) ))).
% 1.20/1.44  thf('12', plain,
% 1.20/1.44      (![X15 : $i, X16 : $i]:
% 1.20/1.44         (((X16) = (X15))
% 1.20/1.44          | ~ (r1_tarski @ (k1_tarski @ X16) @ (k1_tarski @ X15)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 1.20/1.44  thf('13', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_relat_1 @ sk_B))
% 1.20/1.44          | ((X0) = (sk_A)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.44  thf('14', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_B)
% 1.20/1.44          | ~ (v1_relat_1 @ sk_B)
% 1.20/1.44          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['10', '13'])).
% 1.20/1.44  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('17', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 1.20/1.44      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.20/1.44  thf('18', plain,
% 1.20/1.44      (![X1 : $i, X3 : $i]:
% 1.20/1.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.20/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.44  thf('19', plain,
% 1.20/1.44      (![X21 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X23) != (k2_relat_1 @ X21))
% 1.20/1.44          | ((X24) = (k1_funct_1 @ X21 @ (sk_D_1 @ X24 @ X21)))
% 1.20/1.44          | ~ (r2_hidden @ X24 @ X23)
% 1.20/1.44          | ~ (v1_funct_1 @ X21)
% 1.20/1.44          | ~ (v1_relat_1 @ X21))),
% 1.20/1.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.20/1.44  thf('20', plain,
% 1.20/1.44      (![X21 : $i, X24 : $i]:
% 1.20/1.44         (~ (v1_relat_1 @ X21)
% 1.20/1.44          | ~ (v1_funct_1 @ X21)
% 1.20/1.44          | ~ (r2_hidden @ X24 @ (k2_relat_1 @ X21))
% 1.20/1.44          | ((X24) = (k1_funct_1 @ X21 @ (sk_D_1 @ X24 @ X21))))),
% 1.20/1.44      inference('simplify', [status(thm)], ['19'])).
% 1.20/1.44  thf('21', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.20/1.44          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 1.20/1.44              = (k1_funct_1 @ X0 @ 
% 1.20/1.44                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['18', '20'])).
% 1.20/1.44  thf('22', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ sk_B)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_B)
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.20/1.44      inference('sup+', [status(thm)], ['17', '21'])).
% 1.20/1.44  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('25', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.20/1.44  thf('26', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['25'])).
% 1.20/1.44  thf('27', plain,
% 1.20/1.44      (![X1 : $i, X3 : $i]:
% 1.20/1.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.20/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.44  thf('28', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ X0)
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['26', '27'])).
% 1.20/1.44  thf('29', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ X0))),
% 1.20/1.44      inference('simplify', [status(thm)], ['28'])).
% 1.20/1.44  thf('30', plain,
% 1.20/1.44      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 1.20/1.44        (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['4', '29'])).
% 1.20/1.44  thf(l3_zfmisc_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.20/1.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.20/1.44  thf('31', plain,
% 1.20/1.44      (![X10 : $i, X11 : $i]:
% 1.20/1.44         (((X11) = (k1_tarski @ X10))
% 1.20/1.44          | ((X11) = (k1_xboole_0))
% 1.20/1.44          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 1.20/1.44      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.20/1.44  thf('32', plain,
% 1.20/1.44      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 1.20/1.44        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.44  thf('33', plain,
% 1.20/1.44      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('34', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 1.20/1.44      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 1.20/1.44  thf(t146_relat_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( v1_relat_1 @ A ) =>
% 1.20/1.44       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.20/1.44  thf('35', plain,
% 1.20/1.44      (![X17 : $i]:
% 1.20/1.44         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 1.20/1.44          | ~ (v1_relat_1 @ X17))),
% 1.20/1.44      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.20/1.44  thf(t151_relat_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( v1_relat_1 @ B ) =>
% 1.20/1.44       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.20/1.44         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.20/1.44  thf('36', plain,
% 1.20/1.44      (![X18 : $i, X19 : $i]:
% 1.20/1.44         (((k9_relat_1 @ X18 @ X19) != (k1_xboole_0))
% 1.20/1.44          | (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 1.20/1.44          | ~ (v1_relat_1 @ X18))),
% 1.20/1.44      inference('cnf', [status(esa)], [t151_relat_1])).
% 1.20/1.44  thf('37', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.20/1.44          | ~ (v1_relat_1 @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ X0)
% 1.20/1.44          | (r1_xboole_0 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['35', '36'])).
% 1.20/1.44  thf('38', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.20/1.44          | ~ (v1_relat_1 @ X0)
% 1.20/1.44          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['37'])).
% 1.20/1.44  thf('39', plain,
% 1.20/1.44      ((((k1_xboole_0) != (k1_xboole_0))
% 1.20/1.44        | ~ (v1_relat_1 @ sk_B)
% 1.20/1.44        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['34', '38'])).
% 1.20/1.44  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('41', plain,
% 1.20/1.44      ((((k1_xboole_0) != (k1_xboole_0))
% 1.20/1.44        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 1.20/1.44      inference('demod', [status(thm)], ['39', '40'])).
% 1.20/1.44  thf('42', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 1.20/1.44      inference('simplify', [status(thm)], ['41'])).
% 1.20/1.44  thf('43', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(l24_zfmisc_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 1.20/1.44  thf('44', plain,
% 1.20/1.44      (![X8 : $i, X9 : $i]:
% 1.20/1.44         (~ (r1_xboole_0 @ (k1_tarski @ X8) @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.20/1.44      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.20/1.44  thf('45', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 1.20/1.44          | ~ (r2_hidden @ sk_A @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['43', '44'])).
% 1.20/1.44  thf('46', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.20/1.44      inference('sup-', [status(thm)], ['42', '45'])).
% 1.20/1.44  thf('47', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('48', plain,
% 1.20/1.44      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 1.20/1.44      inference('sup+', [status(thm)], ['0', '1'])).
% 1.20/1.44  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))),
% 1.20/1.44      inference('sup+', [status(thm)], ['47', '48'])).
% 1.20/1.44  thf('50', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 1.20/1.44      inference('demod', [status(thm)], ['49', '50'])).
% 1.20/1.44  thf('52', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('53', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i]:
% 1.20/1.44         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 1.20/1.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.20/1.44  thf('54', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0) | (r2_hidden @ sk_A @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.44  thf('55', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.20/1.44      inference('sup-', [status(thm)], ['51', '54'])).
% 1.20/1.44  thf('56', plain, ($false), inference('demod', [status(thm)], ['46', '55'])).
% 1.20/1.44  
% 1.20/1.44  % SZS output end Refutation
% 1.20/1.44  
% 1.20/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
