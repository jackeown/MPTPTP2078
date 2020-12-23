%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x7MwZGcQBS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 182 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :  532 (1577 expanded)
%              Number of equality atoms :   41 ( 146 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k11_relat_1 @ X34 @ X35 )
        = ( k9_relat_1 @ X34 @ ( k1_tarski @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X49 )
      | ~ ( r1_tarski @ X48 @ ( k1_relat_1 @ X49 ) )
      | ( ( k9_relat_1 @ X49 @ X48 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('10',plain,
    ( ( ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
      & ( ( k11_relat_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('25',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ X38 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('26',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X50 @ ( k11_relat_1 @ X51 @ X52 ) )
      | ( r2_hidden @ ( k4_tarski @ X52 @ X50 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('28',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X41 @ X42 ) @ X43 )
      | ( r2_hidden @ X41 @ X44 )
      | ( X44
       != ( k1_relat_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('29',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X41 @ ( k1_relat_1 @ X43 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X41 @ X42 ) @ X43 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('32',plain,
    ( ( v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X53: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X53 ) @ ( sk_C_2 @ X53 ) ) @ X53 )
      | ( X53 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('36',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X50 @ ( k11_relat_1 @ X51 @ X52 ) )
      | ( r2_hidden @ ( k4_tarski @ X52 @ X50 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ X1 @ X0 ) ) @ ( sk_C_2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','21'])).

thf('43',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X41 @ ( k1_relat_1 @ X43 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X41 @ X42 ) @ X43 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['24','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x7MwZGcQBS
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:44:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 77 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.21/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(t205_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.48         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.48            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.21/0.48        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(d16_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X34 : $i, X35 : $i]:
% 0.21/0.48         (((k11_relat_1 @ X34 @ X35) = (k9_relat_1 @ X34 @ (k1_tarski @ X35)))
% 0.21/0.48          | ~ (v1_relat_1 @ X34))),
% 0.21/0.48      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf(l1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X29 : $i, X31 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_tarski @ X29) @ X31) | ~ (r2_hidden @ X29 @ X31))),
% 0.21/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B_2)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf(t152_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.48            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X48 : $i, X49 : $i]:
% 0.21/0.48         (((X48) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X49)
% 0.21/0.48          | ~ (r1_tarski @ X48 @ (k1_relat_1 @ X49))
% 0.21/0.48          | ((k9_relat_1 @ X49 @ X48) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B_2)
% 0.21/0.48         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.21/0.48         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(t1_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.48  thf(t49_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X32 : $i, X33 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k1_tarski @ X32) @ X33) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.48  thf('15', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B_2)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '16'])).
% 0.21/0.48  thf('18', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.21/0.48       ~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.21/0.48       (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('23', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['3', '21', '22'])).
% 0.21/0.48  thf('24', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.21/0.48  thf(d1_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.48              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X38 : $i]: ((v1_relat_1 @ X38) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.48  thf(t204_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.48         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X50 @ (k11_relat_1 @ X51 @ X52))
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X52 @ X50) @ X51)
% 0.21/0.48          | ~ (v1_relat_1 @ X51))),
% 0.21/0.48      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.21/0.48             X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf(d4_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X41 @ X42) @ X43)
% 0.21/0.48          | (r2_hidden @ X41 @ X44)
% 0.21/0.48          | ((X44) != (k1_relat_1 @ X43)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.48         ((r2_hidden @ X41 @ (k1_relat_1 @ X43))
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X41 @ X42) @ X43))),
% 0.21/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | (v1_relat_1 @ (k11_relat_1 @ X0 @ X1))
% 0.21/0.48          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '29'])).
% 0.21/0.48  thf('31', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) | ~ (v1_relat_1 @ sk_B_2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf('33', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain, ((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf(t56_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.21/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X53 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X53) @ (sk_C_2 @ X53)) @ X53)
% 0.21/0.48          | ((X53) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X53))),
% 0.21/0.48      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X50 @ (k11_relat_1 @ X51 @ X52))
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X52 @ X50) @ X51)
% 0.21/0.48          | ~ (v1_relat_1 @ X51))),
% 0.21/0.48      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.21/0.48          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ X0 @ 
% 0.21/0.48              (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ X1 @ X0)) @ 
% 0.21/0.48               (sk_C_2 @ (k11_relat_1 @ X1 @ X0)))) @ 
% 0.21/0.48             X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((r2_hidden @ 
% 0.21/0.48         (k4_tarski @ sk_A @ 
% 0.21/0.48          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.48           (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.21/0.48         sk_B_2)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B_2)
% 0.21/0.48        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.48  thf('39', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (((r2_hidden @ 
% 0.21/0.48         (k4_tarski @ sk_A @ 
% 0.21/0.48          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.48           (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.21/0.48         sk_B_2)
% 0.21/0.48        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('42', plain, (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['3', '21'])).
% 0.21/0.48  thf('43', plain, (((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      ((r2_hidden @ 
% 0.21/0.48        (k4_tarski @ sk_A @ 
% 0.21/0.48         (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.48          (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.21/0.48        sk_B_2)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.48         ((r2_hidden @ X41 @ (k1_relat_1 @ X43))
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X41 @ X42) @ X43))),
% 0.21/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.48  thf('46', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain, ($false), inference('demod', [status(thm)], ['24', '46'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
