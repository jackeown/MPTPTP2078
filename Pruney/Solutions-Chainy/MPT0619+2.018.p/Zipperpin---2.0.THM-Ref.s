%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AaKGcT2tJw

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:22 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 177 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  614 (1783 expanded)
%              Number of equality atoms :   65 ( 211 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

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

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ( ( k11_relat_1 @ X20 @ X21 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('21',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('30',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','23'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( sk_C_1 @ X12 @ X11 )
       != X12 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','23'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AaKGcT2tJw
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 2.41/2.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.41/2.58  % Solved by: fo/fo7.sh
% 2.41/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.41/2.58  % done 798 iterations in 2.121s
% 2.41/2.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.41/2.58  % SZS output start Refutation
% 2.41/2.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.41/2.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.41/2.58  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 2.41/2.58  thf(sk_B_type, type, sk_B: $i).
% 2.41/2.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.41/2.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.41/2.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.41/2.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.41/2.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.41/2.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.41/2.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.41/2.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.41/2.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.41/2.58  thf(sk_A_type, type, sk_A: $i).
% 2.41/2.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.41/2.58  thf(t41_zfmisc_1, axiom,
% 2.41/2.58    (![A:$i,B:$i]:
% 2.41/2.58     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.41/2.58          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 2.41/2.58  thf('0', plain,
% 2.41/2.58      (![X11 : $i, X12 : $i]:
% 2.41/2.58         (((X11) = (k1_xboole_0))
% 2.41/2.58          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X11)
% 2.41/2.58          | ((X11) = (k1_tarski @ X12)))),
% 2.41/2.58      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 2.41/2.58  thf(t14_funct_1, conjecture,
% 2.41/2.58    (![A:$i,B:$i]:
% 2.41/2.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.41/2.58       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.41/2.58         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 2.41/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.41/2.58    (~( ![A:$i,B:$i]:
% 2.41/2.58        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.41/2.58          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.41/2.58            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 2.41/2.58    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 2.41/2.58  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf(t146_relat_1, axiom,
% 2.41/2.58    (![A:$i]:
% 2.41/2.58     ( ( v1_relat_1 @ A ) =>
% 2.41/2.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.41/2.58  thf('2', plain,
% 2.41/2.58      (![X19 : $i]:
% 2.41/2.58         (((k9_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (k2_relat_1 @ X19))
% 2.41/2.58          | ~ (v1_relat_1 @ X19))),
% 2.41/2.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.41/2.58  thf('3', plain,
% 2.41/2.58      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 2.41/2.58        | ~ (v1_relat_1 @ sk_B))),
% 2.41/2.58      inference('sup+', [status(thm)], ['1', '2'])).
% 2.41/2.58  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('5', plain,
% 2.41/2.58      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 2.41/2.58      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.58  thf(t143_relat_1, axiom,
% 2.41/2.58    (![A:$i,B:$i,C:$i]:
% 2.41/2.58     ( ( v1_relat_1 @ C ) =>
% 2.41/2.58       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 2.41/2.58         ( ?[D:$i]:
% 2.41/2.58           ( ( r2_hidden @ D @ B ) & 
% 2.41/2.58             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 2.41/2.58             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 2.41/2.58  thf('6', plain,
% 2.41/2.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 2.41/2.58          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 2.41/2.58          | ~ (v1_relat_1 @ X18))),
% 2.41/2.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 2.41/2.58  thf('7', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 2.41/2.58          | ~ (v1_relat_1 @ sk_B)
% 2.41/2.58          | (r2_hidden @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ 
% 2.41/2.58             (k1_tarski @ sk_A)))),
% 2.41/2.58      inference('sup-', [status(thm)], ['5', '6'])).
% 2.41/2.58  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('9', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 2.41/2.58          | (r2_hidden @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ 
% 2.41/2.58             (k1_tarski @ sk_A)))),
% 2.41/2.58      inference('demod', [status(thm)], ['7', '8'])).
% 2.41/2.58  thf('10', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 2.41/2.58              (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 2.41/2.58             (k1_tarski @ sk_A)))),
% 2.41/2.58      inference('sup-', [status(thm)], ['0', '9'])).
% 2.41/2.58  thf(d1_tarski, axiom,
% 2.41/2.58    (![A:$i,B:$i]:
% 2.41/2.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.41/2.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.41/2.58  thf('11', plain,
% 2.41/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.58         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 2.41/2.58      inference('cnf', [status(esa)], [d1_tarski])).
% 2.41/2.58  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.41/2.58      inference('simplify', [status(thm)], ['11'])).
% 2.41/2.58  thf('13', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf(t205_relat_1, axiom,
% 2.41/2.58    (![A:$i,B:$i]:
% 2.41/2.58     ( ( v1_relat_1 @ B ) =>
% 2.41/2.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 2.41/2.58         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 2.41/2.58  thf('14', plain,
% 2.41/2.58      (![X20 : $i, X21 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 2.41/2.58          | ((k11_relat_1 @ X20 @ X21) != (k1_xboole_0))
% 2.41/2.58          | ~ (v1_relat_1 @ X20))),
% 2.41/2.58      inference('cnf', [status(esa)], [t205_relat_1])).
% 2.41/2.58  thf('15', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.41/2.58          | ~ (v1_relat_1 @ sk_B)
% 2.41/2.58          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 2.41/2.58      inference('sup-', [status(thm)], ['13', '14'])).
% 2.41/2.58  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('17', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.41/2.58          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 2.41/2.58      inference('demod', [status(thm)], ['15', '16'])).
% 2.41/2.58  thf('18', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 2.41/2.58      inference('sup-', [status(thm)], ['12', '17'])).
% 2.41/2.58  thf('19', plain,
% 2.41/2.58      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 2.41/2.58      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.58  thf(d16_relat_1, axiom,
% 2.41/2.58    (![A:$i]:
% 2.41/2.58     ( ( v1_relat_1 @ A ) =>
% 2.41/2.58       ( ![B:$i]:
% 2.41/2.58         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 2.41/2.58  thf('20', plain,
% 2.41/2.58      (![X13 : $i, X14 : $i]:
% 2.41/2.58         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 2.41/2.58          | ~ (v1_relat_1 @ X13))),
% 2.41/2.58      inference('cnf', [status(esa)], [d16_relat_1])).
% 2.41/2.58  thf('21', plain,
% 2.41/2.58      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 2.41/2.58        | ~ (v1_relat_1 @ sk_B))),
% 2.41/2.58      inference('sup+', [status(thm)], ['19', '20'])).
% 2.41/2.58  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('23', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.41/2.58      inference('demod', [status(thm)], ['21', '22'])).
% 2.41/2.58  thf('24', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 2.41/2.58      inference('demod', [status(thm)], ['18', '23'])).
% 2.41/2.58  thf('25', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 2.41/2.58              (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 2.41/2.58             (k1_tarski @ sk_A)))),
% 2.41/2.58      inference('simplify_reflect-', [status(thm)], ['10', '24'])).
% 2.41/2.58  thf('26', plain,
% 2.41/2.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 2.41/2.58      inference('cnf', [status(esa)], [d1_tarski])).
% 2.41/2.58  thf('27', plain,
% 2.41/2.58      (![X0 : $i, X3 : $i]:
% 2.41/2.58         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.41/2.58      inference('simplify', [status(thm)], ['26'])).
% 2.41/2.58  thf('28', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 2.41/2.58              (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) = (sk_A)))),
% 2.41/2.58      inference('sup-', [status(thm)], ['25', '27'])).
% 2.41/2.58  thf('29', plain,
% 2.41/2.58      (![X11 : $i, X12 : $i]:
% 2.41/2.58         (((X11) = (k1_xboole_0))
% 2.41/2.58          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X11)
% 2.41/2.58          | ((X11) = (k1_tarski @ X12)))),
% 2.41/2.58      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 2.41/2.58  thf('30', plain,
% 2.41/2.58      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 2.41/2.58      inference('demod', [status(thm)], ['3', '4'])).
% 2.41/2.58  thf('31', plain,
% 2.41/2.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 2.41/2.58          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 2.41/2.58          | ~ (v1_relat_1 @ X18))),
% 2.41/2.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 2.41/2.58  thf('32', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 2.41/2.58          | ~ (v1_relat_1 @ sk_B)
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (k4_tarski @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ X0) @ sk_B))),
% 2.41/2.58      inference('sup-', [status(thm)], ['30', '31'])).
% 2.41/2.58  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('34', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (k4_tarski @ (sk_D @ sk_B @ (k1_tarski @ sk_A) @ X0) @ X0) @ sk_B))),
% 2.41/2.58      inference('demod', [status(thm)], ['32', '33'])).
% 2.41/2.58  thf('35', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (k4_tarski @ 
% 2.41/2.58              (sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 2.41/2.58               (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 2.41/2.58              (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 2.41/2.58             sk_B))),
% 2.41/2.58      inference('sup-', [status(thm)], ['29', '34'])).
% 2.41/2.58  thf('36', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 2.41/2.58      inference('demod', [status(thm)], ['18', '23'])).
% 2.41/2.58  thf('37', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (k4_tarski @ 
% 2.41/2.58              (sk_D @ sk_B @ (k1_tarski @ sk_A) @ 
% 2.41/2.58               (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 2.41/2.58              (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 2.41/2.58             sk_B))),
% 2.41/2.58      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 2.41/2.58  thf('38', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         ((r2_hidden @ 
% 2.41/2.58           (k4_tarski @ sk_A @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B)
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 2.41/2.58      inference('sup+', [status(thm)], ['28', '37'])).
% 2.41/2.58  thf('39', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | (r2_hidden @ 
% 2.41/2.58             (k4_tarski @ sk_A @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 2.41/2.58      inference('simplify', [status(thm)], ['38'])).
% 2.41/2.58  thf(t8_funct_1, axiom,
% 2.41/2.58    (![A:$i,B:$i,C:$i]:
% 2.41/2.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.41/2.58       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 2.41/2.58         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 2.41/2.58           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 2.41/2.58  thf('40', plain,
% 2.41/2.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.41/2.58         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 2.41/2.58          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 2.41/2.58          | ~ (v1_funct_1 @ X23)
% 2.41/2.58          | ~ (v1_relat_1 @ X23))),
% 2.41/2.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 2.41/2.58  thf('41', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ~ (v1_relat_1 @ sk_B)
% 2.41/2.58          | ~ (v1_funct_1 @ sk_B)
% 2.41/2.58          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 2.41/2.58      inference('sup-', [status(thm)], ['39', '40'])).
% 2.41/2.58  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('44', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 2.41/2.58      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.41/2.58  thf('45', plain,
% 2.41/2.58      (![X11 : $i, X12 : $i]:
% 2.41/2.58         (((X11) = (k1_xboole_0))
% 2.41/2.58          | ((sk_C_1 @ X12 @ X11) != (X12))
% 2.41/2.58          | ((X11) = (k1_tarski @ X12)))),
% 2.41/2.58      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 2.41/2.58  thf('46', plain,
% 2.41/2.58      (![X0 : $i]:
% 2.41/2.58         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 2.41/2.58          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 2.41/2.58      inference('sup-', [status(thm)], ['44', '45'])).
% 2.41/2.58  thf('47', plain,
% 2.41/2.58      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 2.41/2.58        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 2.41/2.58      inference('simplify', [status(thm)], ['46'])).
% 2.41/2.58  thf('48', plain,
% 2.41/2.58      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 2.41/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.58  thf('49', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 2.41/2.58      inference('demod', [status(thm)], ['18', '23'])).
% 2.41/2.58  thf('50', plain, ($false),
% 2.41/2.58      inference('simplify_reflect-', [status(thm)], ['47', '48', '49'])).
% 2.41/2.58  
% 2.41/2.58  % SZS output end Refutation
% 2.41/2.58  
% 2.41/2.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
