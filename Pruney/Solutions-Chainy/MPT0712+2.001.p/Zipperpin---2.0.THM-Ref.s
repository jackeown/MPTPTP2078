%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oo3DMxByW3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:13 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 116 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  578 ( 916 expanded)
%              Number of equality atoms :   37 (  50 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k11_relat_1 @ X24 @ X25 )
        = k1_xboole_0 )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k11_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k9_relat_1 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k9_relat_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('26',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k9_relat_1 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','45','46'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( ( k11_relat_1 @ X31 @ X30 )
        = ( k1_tarski @ ( k1_funct_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['8','52','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oo3DMxByW3
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 216 iterations in 0.109s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(d16_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.39/0.57  thf(t148_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.39/0.57          | ~ (v1_relat_1 @ X20))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf(t167_funct_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( r1_tarski @
% 0.39/0.57         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.39/0.57         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i]:
% 0.39/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57          ( r1_tarski @
% 0.39/0.57            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.39/0.57            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (~ (r1_tarski @ 
% 0.39/0.57          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.39/0.57          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.57           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.57          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k11_relat_1 @ sk_B @ sk_A) @ 
% 0.39/0.57           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.57  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (~ (r1_tarski @ (k11_relat_1 @ sk_B @ sk_A) @ 
% 0.39/0.57          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(t71_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.57  thf('9', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf(t205_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.39/0.57         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X24 @ X25) = (k1_xboole_0))
% 0.39/0.57          | (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.39/0.57          | ~ (v1_relat_1 @ X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r2_hidden @ X1 @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.57          | ((k11_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf(fc3_funct_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.39/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.57  thf('12', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r2_hidden @ X1 @ X0)
% 0.39/0.57          | ((k11_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k1_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.39/0.57  thf(t151_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.57         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X22 @ X23) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.39/0.57          | ~ (v1_relat_1 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.57          | (r2_hidden @ X0 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.39/0.57          | (r1_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ (k1_tarski @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['13', '17'])).
% 0.39/0.57  thf('19', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.57  thf('20', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.57          | (r2_hidden @ X0 @ X1)
% 0.39/0.57          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.39/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i]:
% 0.39/0.57         (~ (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.39/0.57          | ((k9_relat_1 @ X22 @ X23) = (k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.39/0.57          | ~ (v1_relat_1 @ X1)
% 0.39/0.57          | ((k9_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.57          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.39/0.57        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf(t146_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X19 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (k2_relat_1 @ X19))
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.39/0.57            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf('31', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X22 @ X23) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.39/0.57          | ~ (v1_relat_1 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((X0) != (k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.57          | (r1_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf('35', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.57  thf('36', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.57  thf('38', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf(t3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.39/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.39/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((r1_tarski @ X0 @ X1)
% 0.39/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.39/0.57          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r1_tarski @ X0 @ X1)
% 0.39/0.57          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.39/0.57          | (r1_tarski @ X0 @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '42'])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.39/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.57  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '44'])).
% 0.39/0.57  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('47', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '45', '46'])).
% 0.39/0.57  thf(t117_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.57         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X30 : $i, X31 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X30 @ (k1_relat_1 @ X31))
% 0.39/0.57          | ((k11_relat_1 @ X31 @ X30) = (k1_tarski @ (k1_funct_1 @ X31 @ X30)))
% 0.39/0.57          | ~ (v1_funct_1 @ X31)
% 0.39/0.57          | ~ (v1_relat_1 @ X31))),
% 0.39/0.57      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.57        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.39/0.57            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.39/0.57  thf(d10_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('54', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.39/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.39/0.57  thf('55', plain, ($false),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '52', '54'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
