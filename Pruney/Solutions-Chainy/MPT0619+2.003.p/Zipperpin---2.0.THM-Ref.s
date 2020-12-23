%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zeAiTjmHAr

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:20 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 105 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :   26
%              Number of atoms          :  569 ( 902 expanded)
%              Number of equality atoms :   66 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k11_relat_1 @ X27 @ X28 )
        = ( k9_relat_1 @ X27 @ ( k1_tarski @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k9_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k7_relat_1 @ X41 @ X40 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
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
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X35 @ X36 ) )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k11_relat_1 @ X33 @ X34 ) )
      | ( r2_hidden @ ( k4_tarski @ X34 @ X32 ) @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X42 @ X44 ) @ X43 )
      | ( X44
        = ( k1_funct_1 @ X43 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( sk_C @ X26 @ X25 )
       != X26 )
      | ( X25
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X37: $i] :
      ( ( ( k2_relat_1 @ X37 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X37 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('46',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zeAiTjmHAr
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:48:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 76 iterations in 0.054s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.18/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.18/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.18/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.49  thf(t41_zfmisc_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.49          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.18/0.49  thf('0', plain,
% 0.18/0.49      (![X25 : $i, X26 : $i]:
% 0.18/0.49         (((X25) = (k1_xboole_0))
% 0.18/0.49          | (r2_hidden @ (sk_C @ X26 @ X25) @ X25)
% 0.18/0.49          | ((X25) = (k1_tarski @ X26)))),
% 0.18/0.49      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.18/0.49  thf(d16_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.18/0.49  thf('1', plain,
% 0.18/0.49      (![X27 : $i, X28 : $i]:
% 0.18/0.49         (((k11_relat_1 @ X27 @ X28) = (k9_relat_1 @ X27 @ (k1_tarski @ X28)))
% 0.18/0.49          | ~ (v1_relat_1 @ X27))),
% 0.18/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.18/0.49  thf(t148_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (![X30 : $i, X31 : $i]:
% 0.18/0.49         (((k2_relat_1 @ (k7_relat_1 @ X30 @ X31)) = (k9_relat_1 @ X30 @ X31))
% 0.18/0.49          | ~ (v1_relat_1 @ X30))),
% 0.18/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.18/0.49  thf(t94_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X40 : $i, X41 : $i]:
% 0.18/0.49         (((k7_relat_1 @ X41 @ X40) = (k5_relat_1 @ (k6_relat_1 @ X40) @ X41))
% 0.18/0.49          | ~ (v1_relat_1 @ X41))),
% 0.18/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.18/0.49  thf(d10_xboole_0, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.18/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.49  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.18/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.18/0.49  thf(t71_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.18/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.18/0.49  thf('6', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.18/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.49  thf(t14_funct_1, conjecture,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.18/0.49       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.18/0.49         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i,B:$i]:
% 0.18/0.49        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.18/0.49          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.18/0.49            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.18/0.49  thf('7', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(t47_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( v1_relat_1 @ B ) =>
% 0.18/0.49           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.18/0.49             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.18/0.49  thf('8', plain,
% 0.18/0.49      (![X35 : $i, X36 : $i]:
% 0.18/0.49         (~ (v1_relat_1 @ X35)
% 0.18/0.49          | ((k2_relat_1 @ (k5_relat_1 @ X35 @ X36)) = (k2_relat_1 @ X36))
% 0.18/0.49          | ~ (r1_tarski @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X35))
% 0.18/0.49          | ~ (v1_relat_1 @ X36))),
% 0.18/0.49      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.18/0.49  thf('9', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ X0))
% 0.18/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.18/0.49          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.18/0.49          | ~ (v1_relat_1 @ X0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.49  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ X0))
% 0.18/0.49          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.18/0.49          | ~ (v1_relat_1 @ X0))),
% 0.18/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('12', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.18/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.18/0.49          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))
% 0.18/0.49              = (k2_relat_1 @ sk_B)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.18/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.18/0.49  thf('13', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.18/0.49  thf('14', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.18/0.49          | ((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))
% 0.18/0.49              = (k2_relat_1 @ sk_B)))),
% 0.18/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.18/0.49  thf('15', plain,
% 0.18/0.49      (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_tarski @ sk_A)) @ sk_B))
% 0.18/0.49         = (k2_relat_1 @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['5', '14'])).
% 0.18/0.49  thf('16', plain,
% 0.18/0.49      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.18/0.49          = (k2_relat_1 @ sk_B))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.18/0.49      inference('sup+', [status(thm)], ['3', '15'])).
% 0.18/0.49  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('18', plain,
% 0.18/0.49      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.18/0.49         = (k2_relat_1 @ sk_B))),
% 0.18/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.18/0.49  thf('19', plain,
% 0.18/0.49      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.18/0.49      inference('sup+', [status(thm)], ['2', '18'])).
% 0.18/0.49  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('21', plain,
% 0.18/0.49      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.18/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.49  thf('22', plain,
% 0.18/0.49      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.18/0.49      inference('sup+', [status(thm)], ['1', '21'])).
% 0.18/0.49  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('24', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.18/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.18/0.49  thf(t204_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ C ) =>
% 0.18/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.18/0.49         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.18/0.49  thf('25', plain,
% 0.18/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X32 @ (k11_relat_1 @ X33 @ X34))
% 0.18/0.49          | (r2_hidden @ (k4_tarski @ X34 @ X32) @ X33)
% 0.18/0.49          | ~ (v1_relat_1 @ X33))),
% 0.18/0.49      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.18/0.49  thf('26', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.18/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.18/0.49          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.49  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('28', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.18/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.18/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.18/0.50  thf('29', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.18/0.50          | (r2_hidden @ 
% 0.18/0.50             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.18/0.50      inference('sup-', [status(thm)], ['0', '28'])).
% 0.18/0.50  thf(t8_funct_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.18/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.18/0.50           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.18/0.50  thf('30', plain,
% 0.18/0.50      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.18/0.50         (~ (r2_hidden @ (k4_tarski @ X42 @ X44) @ X43)
% 0.18/0.50          | ((X44) = (k1_funct_1 @ X43 @ X42))
% 0.18/0.50          | ~ (v1_funct_1 @ X43)
% 0.18/0.50          | ~ (v1_relat_1 @ X43))),
% 0.18/0.50      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.18/0.50  thf('31', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.18/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.18/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.18/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.50  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('34', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.18/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.18/0.50      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.18/0.50  thf('35', plain,
% 0.18/0.50      (![X25 : $i, X26 : $i]:
% 0.18/0.50         (((X25) = (k1_xboole_0))
% 0.18/0.50          | ((sk_C @ X26 @ X25) != (X26))
% 0.18/0.50          | ((X25) = (k1_tarski @ X26)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.18/0.50  thf('36', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.18/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.50  thf('37', plain,
% 0.18/0.50      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.18/0.50        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.18/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.18/0.50  thf('38', plain,
% 0.18/0.50      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('39', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.18/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.18/0.50  thf(t65_relat_1, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( v1_relat_1 @ A ) =>
% 0.18/0.50       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.50         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.50  thf('40', plain,
% 0.18/0.50      (![X37 : $i]:
% 0.18/0.50         (((k2_relat_1 @ X37) != (k1_xboole_0))
% 0.18/0.50          | ((k1_relat_1 @ X37) = (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ X37))),
% 0.18/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.18/0.50  thf('41', plain,
% 0.18/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.18/0.50        | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.18/0.50  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('43', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('44', plain,
% 0.18/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.18/0.50      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.18/0.50  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.18/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.18/0.50  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.18/0.50  thf('46', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X24))),
% 0.18/0.50      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.18/0.50  thf('47', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.18/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.18/0.50  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.50  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.18/0.50  
% 0.18/0.50  % SZS output end Refutation
% 0.18/0.50  
% 0.18/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
