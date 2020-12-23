%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cB7vtGNN10

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:22 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 172 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  693 (1750 expanded)
%              Number of equality atoms :   89 ( 221 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k11_relat_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ( r2_hidden @ X35 @ ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X15 ) @ X15 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X30 @ X28 ) @ X30 ) @ X28 )
      | ( X29
       != ( k2_relat_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('10',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X30 @ X28 ) @ X30 ) @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k2_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X19 @ X22 )
      | ( X22
       != ( k1_relat_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X34 ) )
      | ( ( k11_relat_1 @ X34 @ X35 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_D_3 @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_D_3 @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_D_3 @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X34 ) )
      | ( ( k11_relat_1 @ X34 @ X35 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X33: $i] :
      ( ( ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('31',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_D_3 @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','37'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ X37 )
      | ( X38
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( sk_C_1 @ X16 @ X15 )
       != X16 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','37'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cB7vtGNN10
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.02/3.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.02/3.21  % Solved by: fo/fo7.sh
% 3.02/3.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.02/3.21  % done 1162 iterations in 2.742s
% 3.02/3.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.02/3.21  % SZS output start Refutation
% 3.02/3.21  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.02/3.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.02/3.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.02/3.21  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 3.02/3.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.02/3.21  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.02/3.21  thf(sk_B_type, type, sk_B: $i).
% 3.02/3.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.02/3.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.02/3.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.02/3.21  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.02/3.21  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 3.02/3.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.02/3.21  thf(sk_A_type, type, sk_A: $i).
% 3.02/3.21  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.02/3.21  thf(t14_funct_1, conjecture,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.02/3.21       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 3.02/3.21         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 3.02/3.21  thf(zf_stmt_0, negated_conjecture,
% 3.02/3.21    (~( ![A:$i,B:$i]:
% 3.02/3.21        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.02/3.21          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 3.02/3.21            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 3.02/3.21    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 3.02/3.21  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf(t205_relat_1, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( v1_relat_1 @ B ) =>
% 3.02/3.21       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 3.02/3.21         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 3.02/3.21  thf('1', plain,
% 3.02/3.21      (![X34 : $i, X35 : $i]:
% 3.02/3.21         (((k11_relat_1 @ X34 @ X35) = (k1_xboole_0))
% 3.02/3.21          | (r2_hidden @ X35 @ (k1_relat_1 @ X34))
% 3.02/3.21          | ~ (v1_relat_1 @ X34))),
% 3.02/3.21      inference('cnf', [status(esa)], [t205_relat_1])).
% 3.02/3.21  thf('2', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 3.02/3.21          | ~ (v1_relat_1 @ sk_B)
% 3.02/3.21          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 3.02/3.21      inference('sup+', [status(thm)], ['0', '1'])).
% 3.02/3.21  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('4', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 3.02/3.21          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 3.02/3.21      inference('demod', [status(thm)], ['2', '3'])).
% 3.02/3.21  thf(d1_tarski, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.02/3.21       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.02/3.21  thf('5', plain,
% 3.02/3.21      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 3.02/3.21      inference('cnf', [status(esa)], [d1_tarski])).
% 3.02/3.21  thf('6', plain,
% 3.02/3.21      (![X0 : $i, X3 : $i]:
% 3.02/3.21         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 3.02/3.21      inference('simplify', [status(thm)], ['5'])).
% 3.02/3.21  thf('7', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['4', '6'])).
% 3.02/3.21  thf(l44_zfmisc_1, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.02/3.21          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 3.02/3.21  thf('8', plain,
% 3.02/3.21      (![X15 : $i, X16 : $i]:
% 3.02/3.21         (((X15) = (k1_xboole_0))
% 3.02/3.21          | (r2_hidden @ (sk_C_1 @ X16 @ X15) @ X15)
% 3.02/3.21          | ((X15) = (k1_tarski @ X16)))),
% 3.02/3.21      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 3.02/3.21  thf(d5_relat_1, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.02/3.21       ( ![C:$i]:
% 3.02/3.21         ( ( r2_hidden @ C @ B ) <=>
% 3.02/3.21           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.02/3.21  thf('9', plain,
% 3.02/3.21      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X30 @ X29)
% 3.02/3.21          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X30 @ X28) @ X30) @ X28)
% 3.02/3.21          | ((X29) != (k2_relat_1 @ X28)))),
% 3.02/3.21      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.02/3.21  thf('10', plain,
% 3.02/3.21      (![X28 : $i, X30 : $i]:
% 3.02/3.21         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X30 @ X28) @ X30) @ X28)
% 3.02/3.21          | ~ (r2_hidden @ X30 @ (k2_relat_1 @ X28)))),
% 3.02/3.21      inference('simplify', [status(thm)], ['9'])).
% 3.02/3.21  thf('11', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 3.02/3.21          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.02/3.21          | (r2_hidden @ 
% 3.02/3.21             (k4_tarski @ (sk_D_3 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 3.02/3.21              (sk_C_1 @ X1 @ (k2_relat_1 @ X0))) @ 
% 3.02/3.21             X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['8', '10'])).
% 3.02/3.21  thf(d4_relat_1, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.02/3.21       ( ![C:$i]:
% 3.02/3.21         ( ( r2_hidden @ C @ B ) <=>
% 3.02/3.21           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.02/3.21  thf('12', plain,
% 3.02/3.21      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.02/3.21         (~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21)
% 3.02/3.21          | (r2_hidden @ X19 @ X22)
% 3.02/3.21          | ((X22) != (k1_relat_1 @ X21)))),
% 3.02/3.21      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.02/3.21  thf('13', plain,
% 3.02/3.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.02/3.21         ((r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 3.02/3.21          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21))),
% 3.02/3.21      inference('simplify', [status(thm)], ['12'])).
% 3.02/3.21  thf('14', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.02/3.21          | ((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 3.02/3.21          | (r2_hidden @ (sk_D_3 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 3.02/3.21             (k1_relat_1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['11', '13'])).
% 3.02/3.21  thf('15', plain,
% 3.02/3.21      (![X34 : $i, X35 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X34))
% 3.02/3.21          | ((k11_relat_1 @ X34 @ X35) != (k1_xboole_0))
% 3.02/3.21          | ~ (v1_relat_1 @ X34))),
% 3.02/3.21      inference('cnf', [status(esa)], [t205_relat_1])).
% 3.02/3.21  thf('16', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 3.02/3.21          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.02/3.21          | ~ (v1_relat_1 @ X0)
% 3.02/3.21          | ((k11_relat_1 @ X0 @ 
% 3.02/3.21              (sk_D_3 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0))
% 3.02/3.21              != (k1_xboole_0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['14', '15'])).
% 3.02/3.21  thf('17', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k1_xboole_0) != (k1_xboole_0))
% 3.02/3.21          | ((sk_D_3 @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 3.02/3.21          | ~ (v1_relat_1 @ sk_B)
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['7', '16'])).
% 3.02/3.21  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('19', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k1_xboole_0) != (k1_xboole_0))
% 3.02/3.21          | ((sk_D_3 @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 3.02/3.21      inference('demod', [status(thm)], ['17', '18'])).
% 3.02/3.21  thf('20', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 3.02/3.21          | ((sk_D_3 @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 3.02/3.21      inference('simplify', [status(thm)], ['19'])).
% 3.02/3.21  thf('21', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 3.02/3.21      inference('cnf', [status(esa)], [d1_tarski])).
% 3.02/3.21  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.02/3.21      inference('simplify', [status(thm)], ['21'])).
% 3.02/3.21  thf('23', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('24', plain,
% 3.02/3.21      (![X34 : $i, X35 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X34))
% 3.02/3.21          | ((k11_relat_1 @ X34 @ X35) != (k1_xboole_0))
% 3.02/3.21          | ~ (v1_relat_1 @ X34))),
% 3.02/3.21      inference('cnf', [status(esa)], [t205_relat_1])).
% 3.02/3.21  thf('25', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 3.02/3.21          | ~ (v1_relat_1 @ sk_B)
% 3.02/3.21          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['23', '24'])).
% 3.02/3.21  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('27', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 3.02/3.21          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 3.02/3.21      inference('demod', [status(thm)], ['25', '26'])).
% 3.02/3.21  thf('28', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['22', '27'])).
% 3.02/3.21  thf('29', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf(t146_relat_1, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( v1_relat_1 @ A ) =>
% 3.02/3.21       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 3.02/3.21  thf('30', plain,
% 3.02/3.21      (![X33 : $i]:
% 3.02/3.21         (((k9_relat_1 @ X33 @ (k1_relat_1 @ X33)) = (k2_relat_1 @ X33))
% 3.02/3.21          | ~ (v1_relat_1 @ X33))),
% 3.02/3.21      inference('cnf', [status(esa)], [t146_relat_1])).
% 3.02/3.21  thf('31', plain,
% 3.02/3.21      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 3.02/3.21        | ~ (v1_relat_1 @ sk_B))),
% 3.02/3.21      inference('sup+', [status(thm)], ['29', '30'])).
% 3.02/3.21  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('33', plain,
% 3.02/3.21      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['31', '32'])).
% 3.02/3.21  thf(d16_relat_1, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( v1_relat_1 @ A ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 3.02/3.21  thf('34', plain,
% 3.02/3.21      (![X17 : $i, X18 : $i]:
% 3.02/3.21         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 3.02/3.21          | ~ (v1_relat_1 @ X17))),
% 3.02/3.21      inference('cnf', [status(esa)], [d16_relat_1])).
% 3.02/3.21  thf('35', plain,
% 3.02/3.21      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 3.02/3.21        | ~ (v1_relat_1 @ sk_B))),
% 3.02/3.21      inference('sup+', [status(thm)], ['33', '34'])).
% 3.02/3.21  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('37', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['35', '36'])).
% 3.02/3.21  thf('38', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 3.02/3.21      inference('demod', [status(thm)], ['28', '37'])).
% 3.02/3.21  thf('39', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ((sk_D_3 @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 3.02/3.21      inference('simplify_reflect-', [status(thm)], ['20', '38'])).
% 3.02/3.21  thf('40', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 3.02/3.21          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.02/3.21          | (r2_hidden @ 
% 3.02/3.21             (k4_tarski @ (sk_D_3 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 3.02/3.21              (sk_C_1 @ X1 @ (k2_relat_1 @ X0))) @ 
% 3.02/3.21             X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['8', '10'])).
% 3.02/3.21  thf('41', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         ((r2_hidden @ 
% 3.02/3.21           (k4_tarski @ sk_A @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B)
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 3.02/3.21      inference('sup+', [status(thm)], ['39', '40'])).
% 3.02/3.21  thf('42', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | (r2_hidden @ 
% 3.02/3.21             (k4_tarski @ sk_A @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 3.02/3.21      inference('simplify', [status(thm)], ['41'])).
% 3.02/3.21  thf('43', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 3.02/3.21      inference('demod', [status(thm)], ['28', '37'])).
% 3.02/3.21  thf('44', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | (r2_hidden @ 
% 3.02/3.21             (k4_tarski @ sk_A @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 3.02/3.21      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 3.02/3.21  thf(t8_funct_1, axiom,
% 3.02/3.21    (![A:$i,B:$i,C:$i]:
% 3.02/3.21     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.02/3.21       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 3.02/3.21         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 3.02/3.21           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 3.02/3.21  thf('45', plain,
% 3.02/3.21      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.02/3.21         (~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ X37)
% 3.02/3.21          | ((X38) = (k1_funct_1 @ X37 @ X36))
% 3.02/3.21          | ~ (v1_funct_1 @ X37)
% 3.02/3.21          | ~ (v1_relat_1 @ X37))),
% 3.02/3.21      inference('cnf', [status(esa)], [t8_funct_1])).
% 3.02/3.21  thf('46', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ~ (v1_relat_1 @ sk_B)
% 3.02/3.21          | ~ (v1_funct_1 @ sk_B)
% 3.02/3.21          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['44', '45'])).
% 3.02/3.21  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('49', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('demod', [status(thm)], ['46', '47', '48'])).
% 3.02/3.21  thf('50', plain,
% 3.02/3.21      (![X15 : $i, X16 : $i]:
% 3.02/3.21         (((X15) = (k1_xboole_0))
% 3.02/3.21          | ((sk_C_1 @ X16 @ X15) != (X16))
% 3.02/3.21          | ((X15) = (k1_tarski @ X16)))),
% 3.02/3.21      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 3.02/3.21  thf('51', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 3.02/3.21          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['49', '50'])).
% 3.02/3.21  thf('52', plain,
% 3.02/3.21      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 3.02/3.21        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 3.02/3.21      inference('simplify', [status(thm)], ['51'])).
% 3.02/3.21  thf('53', plain,
% 3.02/3.21      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('54', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 3.02/3.21      inference('demod', [status(thm)], ['28', '37'])).
% 3.02/3.21  thf('55', plain, ($false),
% 3.02/3.21      inference('simplify_reflect-', [status(thm)], ['52', '53', '54'])).
% 3.02/3.21  
% 3.02/3.21  % SZS output end Refutation
% 3.02/3.21  
% 3.02/3.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
