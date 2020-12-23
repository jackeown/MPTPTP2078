%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s739uVq2Bm

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 107 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  612 (1038 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t204_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t204_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ X30 @ ( k9_relat_1 @ X31 @ X29 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X33 ) @ X34 )
      | ( r2_hidden @ X32 @ ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['2','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k9_relat_1 @ X31 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X31 @ X29 @ X30 ) @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k9_relat_1 @ X31 @ X29 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X29 @ X30 ) @ X29 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('43',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s739uVq2Bm
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:15:23 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 121 iterations in 0.046s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.23/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.52  thf(t204_relat_1, conjecture,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ C ) =>
% 0.23/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.52         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.52        ( ( v1_relat_1 @ C ) =>
% 0.23/0.52          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.52            ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t204_relat_1])).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.23/0.52        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.23/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf(d16_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X26 : $i, X27 : $i]:
% 0.23/0.52         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 0.23/0.52          | ~ (v1_relat_1 @ X26))),
% 0.23/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.23/0.52  thf(t69_enumset1, axiom,
% 0.23/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.52  thf('3', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.23/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.52  thf(d2_tarski, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.23/0.52       ( ![D:$i]:
% 0.23/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.52         (((X1) != (X0))
% 0.23/0.52          | (r2_hidden @ X1 @ X2)
% 0.23/0.52          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.23/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.52  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['3', '5'])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.23/0.52        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('split', [status(esa)], ['7'])).
% 0.23/0.52  thf(t143_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ C ) =>
% 0.23/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.23/0.52         ( ?[D:$i]:
% 0.23/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.23/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.23/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X28 @ X29)
% 0.23/0.52          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ X31)
% 0.23/0.52          | ~ (r2_hidden @ X28 @ (k1_relat_1 @ X31))
% 0.23/0.52          | (r2_hidden @ X30 @ (k9_relat_1 @ X31 @ X29))
% 0.23/0.52          | ~ (v1_relat_1 @ X31))),
% 0.23/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      ((![X0 : $i]:
% 0.23/0.52          (~ (v1_relat_1 @ sk_C)
% 0.23/0.52           | (r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 0.23/0.52           | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.23/0.52           | ~ (r2_hidden @ sk_A @ X0)))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.52  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('split', [status(esa)], ['7'])).
% 0.23/0.52  thf(t20_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ C ) =>
% 0.23/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.23/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.23/0.52           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.23/0.52         (~ (r2_hidden @ (k4_tarski @ X32 @ X33) @ X34)
% 0.23/0.52          | (r2_hidden @ X32 @ (k1_relat_1 @ X34))
% 0.23/0.52          | ~ (v1_relat_1 @ X34))),
% 0.23/0.52      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.52  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      ((![X0 : $i]:
% 0.23/0.52          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 0.23/0.52           | ~ (r2_hidden @ sk_A @ X0)))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('demod', [status(thm)], ['10', '11', '16'])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A))))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['6', '17'])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      ((((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.23/0.52         | ~ (v1_relat_1 @ sk_C)))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('sup+', [status(thm)], ['2', '18'])).
% 0.23/0.52  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.23/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.23/0.52         <= (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.23/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.23/0.52       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.52      inference('split', [status(esa)], ['7'])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.23/0.52         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['7'])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      (![X26 : $i, X27 : $i]:
% 0.23/0.52         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 0.23/0.52          | ~ (v1_relat_1 @ X26))),
% 0.23/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X30 @ (k9_relat_1 @ X31 @ X29))
% 0.23/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X31 @ X29 @ X30) @ X30) @ X31)
% 0.23/0.52          | ~ (v1_relat_1 @ X31))),
% 0.23/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | (r2_hidden @ 
% 0.23/0.52             (k4_tarski @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.52         ((r2_hidden @ 
% 0.23/0.52           (k4_tarski @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.23/0.52  thf('30', plain,
% 0.23/0.52      (((~ (v1_relat_1 @ sk_C)
% 0.23/0.52         | (r2_hidden @ 
% 0.23/0.52            (k4_tarski @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.23/0.52            sk_C)))
% 0.23/0.52         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['25', '29'])).
% 0.23/0.52  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (((r2_hidden @ 
% 0.23/0.52         (k4_tarski @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.23/0.52         sk_C)) <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.52  thf('33', plain,
% 0.23/0.52      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.23/0.52         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.52      inference('split', [status(esa)], ['7'])).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (![X26 : $i, X27 : $i]:
% 0.23/0.52         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 0.23/0.52          | ~ (v1_relat_1 @ X26))),
% 0.23/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X30 @ (k9_relat_1 @ X31 @ X29))
% 0.23/0.52          | (r2_hidden @ (sk_D_1 @ X31 @ X29 @ X30) @ X29)
% 0.23/0.52          | ~ (v1_relat_1 @ X31))),
% 0.23/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.52  thf('36', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | (r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ 
% 0.23/0.52             (k1_tarski @ X0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('37', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.52         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      (((~ (v1_relat_1 @ sk_C)
% 0.23/0.52         | (r2_hidden @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.23/0.53            (k1_tarski @ sk_A))))
% 0.23/0.53         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['33', '37'])).
% 0.23/0.53  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('40', plain,
% 0.23/0.53      (((r2_hidden @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.23/0.53         (k1_tarski @ sk_A)))
% 0.23/0.53         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.53  thf('41', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.23/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.23/0.53          | ((X4) = (X3))
% 0.23/0.53          | ((X4) = (X0))
% 0.23/0.53          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.23/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.23/0.53  thf('43', plain,
% 0.23/0.53      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.23/0.53         (((X4) = (X0))
% 0.23/0.53          | ((X4) = (X3))
% 0.23/0.53          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.23/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.23/0.53  thf('44', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['41', '43'])).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.23/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.23/0.53  thf('46', plain,
% 0.23/0.53      ((((sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) = (sk_A)))
% 0.23/0.53         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['40', '45'])).
% 0.23/0.53  thf('47', plain,
% 0.23/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.23/0.53         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['32', '46'])).
% 0.23/0.53  thf('48', plain,
% 0.23/0.53      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.23/0.53         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.23/0.53      inference('split', [status(esa)], ['0'])).
% 0.23/0.53  thf('49', plain,
% 0.23/0.53      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.23/0.53       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.23/0.53  thf('50', plain, ($false),
% 0.23/0.53      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '49'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
