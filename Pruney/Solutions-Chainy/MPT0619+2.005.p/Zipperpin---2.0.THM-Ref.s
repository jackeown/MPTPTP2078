%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WwgCTo9E5j

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 206 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  596 (1928 expanded)
%              Number of equality atoms :   62 ( 212 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X33 @ X32 ) @ X32 )
      | ( X32
        = ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k11_relat_1 @ X34 @ X35 )
        = ( k9_relat_1 @ X34 @ ( k1_tarski @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ X49 @ X48 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X47: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

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

thf('7',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X44 @ X45 ) )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_tarski @ sk_A ) ) @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k11_relat_1 @ X40 @ X41 ) )
      | ( r2_hidden @ ( k4_tarski @ X41 @ X39 ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ ( k1_tarski @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ X42 ) )
      | ( ( k11_relat_1 @ X42 @ X43 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('40',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','40'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X50 @ X52 ) @ X51 )
      | ( X52
        = ( k1_funct_1 @ X51 @ X50 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( ( sk_C @ X33 @ X32 )
       != X33 )
      | ( X32
        = ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WwgCTo9E5j
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 156 iterations in 0.066s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(t41_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X32 : $i, X33 : $i]:
% 0.22/0.52         (((X32) = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ (sk_C @ X33 @ X32) @ X32)
% 0.22/0.52          | ((X32) = (k1_tarski @ X33)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.52  thf(d16_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X34 : $i, X35 : $i]:
% 0.22/0.52         (((k11_relat_1 @ X34 @ X35) = (k9_relat_1 @ X34 @ (k1_tarski @ X35)))
% 0.22/0.52          | ~ (v1_relat_1 @ X34))),
% 0.22/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.52  thf(t148_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X37 : $i, X38 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 0.22/0.52          | ~ (v1_relat_1 @ X37))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf(t94_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X48 : $i, X49 : $i]:
% 0.22/0.52         (((k7_relat_1 @ X49 @ X48) = (k5_relat_1 @ (k6_relat_1 @ X48) @ X49))
% 0.22/0.52          | ~ (v1_relat_1 @ X49))),
% 0.22/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.52  thf(t71_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.52  thf('6', plain, (![X47 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.52  thf(t14_funct_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.52         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.52            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.22/0.52  thf('7', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t47_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.52             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X44 : $i, X45 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X44)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X44 @ X45)) = (k2_relat_1 @ X45))
% 0.22/0.52          | ~ (r1_tarski @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X44))
% 0.22/0.52          | ~ (v1_relat_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ X0))
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))
% 0.22/0.52              = (k2_relat_1 @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '11'])).
% 0.22/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.52  thf('13', plain, (![X36 : $i]: (v1_relat_1 @ (k6_relat_1 @ X36))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))
% 0.22/0.52              = (k2_relat_1 @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_tarski @ sk_A)) @ sk_B))
% 0.22/0.52         = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.22/0.52          = (k2_relat_1 @ sk_B))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '15'])).
% 0.22/0.52  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.22/0.52         = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '18'])).
% 0.22/0.52  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '21'])).
% 0.22/0.52  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('24', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf(t204_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ C ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X39 @ (k11_relat_1 @ X40 @ X41))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X41 @ X39) @ X40)
% 0.22/0.52          | ~ (v1_relat_1 @ X40))),
% 0.22/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '28'])).
% 0.22/0.52  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.52  thf(l1_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X25 : $i, X26 : $i]:
% 0.22/0.52         ((r2_hidden @ X25 @ X26) | ~ (r1_tarski @ (k1_tarski @ X25) @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.52  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t205_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.52         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X42 : $i, X43 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X43 @ (k1_relat_1 @ X42))
% 0.22/0.52          | ((k11_relat_1 @ X42 @ X43) != (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X42))),
% 0.22/0.52      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.52          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.22/0.52  thf('39', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('40', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['29', '40'])).
% 0.22/0.52  thf(t8_funct_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k4_tarski @ X50 @ X52) @ X51)
% 0.22/0.52          | ((X52) = (k1_funct_1 @ X51 @ X50))
% 0.22/0.52          | ~ (v1_funct_1 @ X51)
% 0.22/0.52          | ~ (v1_relat_1 @ X51))),
% 0.22/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.53          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.53  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.53          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i]:
% 0.22/0.53         (((X32) = (k1_xboole_0))
% 0.22/0.53          | ((sk_C @ X33 @ X32) != (X33))
% 0.22/0.53          | ((X32) = (k1_tarski @ X33)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.22/0.53          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.53          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.53          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.53        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('51', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.53  thf('52', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['49', '50', '51'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
