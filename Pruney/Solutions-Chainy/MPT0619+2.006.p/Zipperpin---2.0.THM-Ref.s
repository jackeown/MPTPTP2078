%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bl1lU5XiUY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 146 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  518 (1311 expanded)
%              Number of equality atoms :   65 ( 162 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X35 ) @ X36 )
      | ( ( k7_relat_1 @ X35 @ X36 )
        = X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k9_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X34 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k9_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','20'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X26 @ X25 ) @ X25 )
      | ( X25
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k11_relat_1 @ X27 @ X28 )
        = ( k9_relat_1 @ X27 @ ( k1_tarski @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X37 @ X39 ) @ X38 )
      | ( X39
        = ( k1_funct_1 @ X38 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( sk_C @ X26 @ X25 )
       != X26 )
      | ( X25
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('45',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bl1lU5XiUY
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 85 iterations in 0.056s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(t14_funct_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.54         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.54            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.20/0.54  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.54  thf(t97_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.54         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X35 : $i, X36 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k1_relat_1 @ X35) @ X36)
% 0.20/0.54          | ((k7_relat_1 @ X35 @ X36) = (X35))
% 0.20/0.54          | ~ (v1_relat_1 @ X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.54  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('7', plain, (((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf(t148_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X29 @ X30)) = (k9_relat_1 @ X29 @ X30))
% 0.20/0.54          | ~ (v1_relat_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf(t65_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X34 : $i]:
% 0.20/0.54         (((k2_relat_1 @ X34) != (k1_xboole_0))
% 0.20/0.54          | ((k1_relat_1 @ X34) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.54          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.20/0.54            = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | ((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.54  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('13', plain, (((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('14', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('16', plain, (((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X29 @ X30)) = (k9_relat_1 @ X29 @ X30))
% 0.20/0.54          | ~ (v1_relat_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((k2_relat_1 @ sk_B) != (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '20'])).
% 0.20/0.54  thf(t41_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.54          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         (((X25) = (k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ (sk_C @ X26 @ X25) @ X25)
% 0.20/0.54          | ((X25) = (k1_tarski @ X26)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.54  thf(d16_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i]:
% 0.20/0.54         (((k11_relat_1 @ X27 @ X28) = (k9_relat_1 @ X27 @ (k1_tarski @ X28)))
% 0.20/0.54          | ~ (v1_relat_1 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_B) = (k11_relat_1 @ sk_B @ sk_A))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('27', plain, (((k2_relat_1 @ sk_B) = (k11_relat_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf(t204_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.54         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.20/0.54          | ~ (v1_relat_1 @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '31'])).
% 0.20/0.54  thf(t8_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.54           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (k4_tarski @ X37 @ X39) @ X38)
% 0.20/0.54          | ((X39) = (k1_funct_1 @ X38 @ X37))
% 0.20/0.54          | ~ (v1_funct_1 @ X38)
% 0.20/0.54          | ~ (v1_relat_1 @ X38))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.54          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         (((X25) = (k1_xboole_0))
% 0.20/0.54          | ((sk_C @ X26 @ X25) != (X26))
% 0.20/0.54          | ((X25) = (k1_tarski @ X26)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.54          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('42', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '42'])).
% 0.20/0.54  thf('44', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.54  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.54  thf('45', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.54  thf('46', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.54  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.54  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
