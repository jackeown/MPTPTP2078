%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3PZ9iMXyl5

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 (  93 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  499 ( 751 expanded)
%              Number of equality atoms :   52 (  77 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('27',plain,(
    ! [X19: $i] :
      ( ( ( k3_xboole_0 @ X19 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('28',plain,
    ( ( ( ( k3_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
        = ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ ( k2_zfmisc_1 @ X13 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_xboole_0
        = ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','33','34','37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k7_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','13','14','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3PZ9iMXyl5
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:12:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 99 iterations in 0.052s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(t95_relat_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( v1_relat_1 @ B ) =>
% 0.19/0.50          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.50            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.50        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.19/0.50       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.50        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('split', [status(esa)], ['2'])).
% 0.19/0.50  thf(t90_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.19/0.50         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]:
% 0.19/0.50         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.19/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.19/0.50          | ~ (v1_relat_1 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.19/0.50  thf(d7_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X2 : $i, X4 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) != (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '6'])).
% 0.19/0.50  thf(t60_relat_1, axiom,
% 0.19/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.50  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.19/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.19/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.19/0.50         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.19/0.50       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.19/0.50       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('split', [status(esa)], ['2'])).
% 0.19/0.50  thf(dt_k7_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('split', [status(esa)], ['2'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      ((((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0)))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]:
% 0.19/0.50         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.19/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.19/0.50          | ~ (v1_relat_1 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.19/0.50            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.19/0.50          | ~ (v1_relat_1 @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (((((k1_xboole_0) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.19/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['20', '23'])).
% 0.19/0.50  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      ((((k1_xboole_0) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.50  thf(t22_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ( k3_xboole_0 @
% 0.19/0.50           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.19/0.50         ( A ) ) ))).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X19 : $i]:
% 0.19/0.50         (((k3_xboole_0 @ X19 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19))) = (
% 0.19/0.50            X19))
% 0.19/0.50          | ~ (v1_relat_1 @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (((((k3_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.19/0.50           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.19/0.50            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.19/0.50           = (k7_relat_1 @ sk_B @ sk_A))
% 0.19/0.50         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.50  thf('29', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.50  thf(t127_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.19/0.50       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k2_zfmisc_1 @ X11 @ X12) @ (k2_zfmisc_1 @ X13 @ X14))
% 0.19/0.50          | ~ (r1_xboole_0 @ X11 @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 0.19/0.50          (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf(t66_xboole_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.50       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X10 : $i]: (((X10) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X10 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.50  thf(t2_boole, axiom,
% 0.19/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (((((k1_xboole_0) = (k7_relat_1 @ sk_B @ sk_A))
% 0.19/0.50         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['28', '33', '34', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (((~ (v1_relat_1 @ sk_B) | ((k1_xboole_0) = (k7_relat_1 @ sk_B @ sk_A))))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '38'])).
% 0.19/0.50  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      ((((k1_xboole_0) = (k7_relat_1 @ sk_B @ sk_A)))
% 0.19/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.19/0.50         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.50         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.50             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.19/0.50       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.50  thf('45', plain, ($false),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['1', '13', '14', '44'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
